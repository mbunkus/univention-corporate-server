#!/usr/bin/python3
# -*- coding: utf-8 -*-
#
# Univention Management Console
#  session handling
#
# Copyright 2006-2020 Univention GmbH
#
# https://www.univention.de/
#
# All rights reserved.
#
# The source code of this program is made available
# under the terms of the GNU Affero General Public License version 3
# (GNU AGPL V3) as published by the Free Software Foundation.
#
# Binary versions of this program provided by Univention to you as
# well as other copyrighted, protected or trademarked materials like
# Logos, graphics, fonts, specific documentations and configurations,
# cryptographic keys etc. are subject to a license agreement between
# you and Univention and not subject to the GNU AGPL V3.
#
# In the case you use this program under the terms of the GNU AGPL V3,
# the program is provided in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public
# License with the Debian GNU/Linux or Univention distribution in file
# /usr/share/common-licenses/AGPL-3; if not, see
# <https://www.gnu.org/licenses/>.

"""Implements several helper classes to handle the state of a session
and the communication with the module processes"""

import base64
import ldap
import os
import time
import json
import traceback
import gzip
import re
import errno
import pipes

import six
from ldap.filter import filter_format

import tornado
import tornado.gen
import tornado.web
import tornado.httpclient
import tornado.curl_httpclient
import pycurl
import notifier
from notifier import threads
from concurrent.futures import ThreadPoolExecutor

import univention.admin.uexceptions as udm_errors

from .message import Request

from ..resources import moduleManager, categoryManager
from ..auth import AuthHandler
from ..pam import PamAuth, PasswordChangeFailed
from ..acl import LDAP_ACLs, ACLs
from ..log import CORE
from ..config import MODULE_INACTIVITY_TIMER, MODULE_DEBUG_LEVEL, MODULE_COMMAND, SERVER_CONNECTION_TIMEOUT, ucr, get_int
from ..locales import I18N, I18N_Manager
from ..base import Base
from ..error import UMC_Error, Unauthorized, BadRequest, Forbidden, ServiceUnavailable, BadGateway
from ..ldap import get_machine_connection, reset_cache as reset_ldap_connection_cache
from ..modules.sanitizers import StringSanitizer, DictSanitizer
from ..modules.decorators import sanitize, sanitize_args, allow_get_request

TEMPUPLOADDIR = '/var/tmp/univention-management-console-frontend'

SessionHandler = None


class CouldNotConnect(Exception):
	pass


def allow_unauthorized(func):
	return func


pool = ThreadPoolExecutor(max_workers=get_int('umc/http/maxthreads', 35))
tornado.httpclient.AsyncHTTPClient.configure('tornado.curl_httpclient.CurlAsyncHTTPClient')  # TODO: move


class ModuleProcess(object):

	"""handles the communication with a UMC module process

	:param str module: name of the module to start
	:param str debug: debug level as a string
	:param str locale: locale to use for the module process
	"""

	def __init__(self, module, debug='0', locale=None):
		self.name = module
		self.socket = '/var/run/univention-management-console/%u-%lu.socket' % (os.getpid(), int(time.time() * 1000))
		modxmllist = moduleManager[module]
		python = '/usr/bin/python3' if any(modxml.python_version == 3 for modxml in modxmllist) else '/usr/bin/python2.7'
		args = [python, MODULE_COMMAND, '-m', module, '-s', self.socket, '-d', str(debug)]
		for modxml in modxmllist:
			if modxml.notifier:
				args.extend(['-n', modxml.notifier])
				break
		if locale:
			args.extend(('-l', '%s' % locale))

		CORE.process('running: %s' % ' '.join(pipes.quote(x) for x in args))
		self.__process = tornado.process.Subprocess(args)  # , stderr=tornado.process.Subprocess.STREAM)
		# self.__process.initialize()
		self.__process.set_exit_callback(self._died)
		self._client = tornado.httpclient.AsyncHTTPClient()

		self._inactivity_timer = None
		self._inactivity_counter = 0
		self._connect_timer = None
		self.__killtimer = None

	@tornado.gen.coroutine
	def connect(self, connect_retries=0):
		if os.path.exists(self.socket):
			raise tornado.gen.Return(True)
		elif connect_retries > 200:
			raise CouldNotConnect('timeout exceeded')
		elif self.__process and self.__process.proc.poll() is not None:
			raise CouldNotConnect('process died')
		else:
			if not connect_retries % 50:
				CORE.info('No connection to module process yet')
			connect_retries += 1
			yield tornado.gen.sleep(0.05)
			yield self.connect(connect_retries)

	@tornado.gen.coroutine
	def request(self, method, uri, headers=None, body=None):
		request = tornado.httpclient.HTTPRequest(
			uri,
			method=method,
			body=body,
			headers=headers,
			allow_nonstandard_methods=True,
			follow_redirects=False,
			connect_timeout=10.0,
			request_timeout=get_int('umc/http/response-timeout', 310) + 2,  # never!
			prepare_curl_callback=lambda curl: curl.setopt(pycurl.UNIX_SOCKET_PATH, self.socket),
		)
		# watch the module's activity and kill it after X seconds inactivity
		self.reset_inactivity_timer()

		try:
			response = yield self._client.fetch(request, raise_error=True)
		except tornado.curl_httpclient.CurlError as exc:
			CORE.warn('Reaching module failed: %s' % (exc,))
			raise CouldNotConnect(exc)
		except tornado.httpclient.HTTPError as exc:
			response = exc.response
			if response is None:  # (599, 'Timeout while connecting', None)
				raise CouldNotConnect(exc)

		self.reset_inactivity_timer()
		raise tornado.gen.Return(response)

	def stop(self):
		# type: () -> None
		CORE.process('ModuleProcess: stopping %r' % (self.pid(),))
		if self.__process:
			tornado.ioloop.IOLoop.instance().add_callback(self.stop_process)

	@tornado.gen.coroutine
	def stop_process(self):
		proc = self.__process.proc
		if proc.poll() is None:
			proc.terminate()
		yield tornado.gen.sleep(3.0)
		if proc.poll() is None:
			proc.kill()
		# TOD: if not succeeds, kill all childs
		CORE.info('ModuleProcess: child stopped')
		self.__process = None

	def _died(self, returncode):
		# type: (int) -> None
		pid = self.pid()
		CORE.process('ModuleProcess: child %d (%s) exited with %d' % (pid, self.name, returncode))
		# if killtimer has been set then remove it
		if self.__killtimer:
			CORE.info('Stopping kill timer)')
			notifier.timer_remove(self.__killtimer)
			self.__killtimer = None
		return
		self.invalidate_all_requests()
		if self._inactivity_timer is not None:
			CORE.warn('Remove inactivity timer')
			notifier.timer_remove(self._inactivity_timer)

	def invalidate_all_requests(self):
		_ = lambda x: x
		raise BadGateway('%s: %s' % (_('Module process died unexpectedly'), self.name))

	def pid(self):
		# type: () -> int
		"""Returns process ID of module process"""
		if self.__process is None:
			return 0
		return self.__process.pid

	def reset_inactivity_timer(self):
		"""Resets the inactivity timer. This timer watches the
		inactivity of the module process. If the module did not receive
		a request for MODULE_INACTIVITY_TIMER seconds the module process
		is shut down to save resources. The timer ticks each seconds to
		handle glitches of the system clock.
		"""
		if self._inactivity_timer is None:
			self._inactivity_timer = notifier.timer_add(1000, self._inactivitiy_tick)

		self._inactivity_counter = MODULE_INACTIVITY_TIMER

	def _inactivitiy_tick(self):
		if self._inactivity_counter > 0:
			self._inactivity_counter -= 1000
			return True
		if self._mod_inactive(self):  # open requests -> waiting
			self._inactivity_counter = MODULE_INACTIVITY_TIMER
			return True

		self._inactivity_timer = None
		self._inactivity_counter = 0

		return False

	def _mod_inactive(self):
		CORE.info('The module %s is inactive for too long. Sending EXIT request to module' % self.name)
		if self.openRequests:
			CORE.info('There are unfinished requests. Waiting for %s' % ', '.join(self.openRequests))
			return True

		# mark as internal so the response will not be forwarded to the client
		req = Request('EXIT', arguments=[self.name, 'internal'])
		self.handle_request_exit(req)

		return False


class User(object):

	__slots__ = ('session', 'username', 'password', 'user_dn', 'auth_type')

	def __init__(self, session):
		self.session = session
		self.username = None
		self.password = None
		self.user_dn = None

	def set_credentials(self, username, password, auth_type):
		self.username = username
		self.password = password
		self.auth_type = auth_type
		self._search_user_dn()
		self.session.acls._reload_acls_and_permitted_commands()
		self.session.processes.update_module_passwords()

	def _search_user_dn(self):
		lo = get_machine_connection(write=False)[0]
		if lo and self.username:
			# get the LDAP DN of the authorized user
			try:
				ldap_dn = lo.searchDn(filter_format('(&(uid=%s)(objectClass=person))', (self.username,)))
			except (ldap.LDAPError, udm_errors.base):
				reset_ldap_connection_cache(lo)
				ldap_dn = None
				CORE.error('Could not get uid for %r: %s' % (self.username, traceback.format_exc()))
			if ldap_dn:
				self.user_dn = ldap_dn[0]
				CORE.info('The LDAP DN for user %s is %s' % (self.username, self.user_dn))

		if not self.user_dn and self.username not in ('root', '__systemsetup__', None):
			CORE.error('The LDAP DN for user %s could not be found (lo=%r)' % (self.username, lo))

	def get_user_ldap_connection(self, **kwargs):
		base = Base()
		base.auth_type = self.auth_type
		base.username = self.username
		base.user_dn = self.user_dn
		base.password = self.password
		return base.get_user_ldap_connection(**kwargs)


class Session(object):

	__slots__ = ('acls', 'user', 'processes', 'authenticated', 'timeout')

	__auth = AuthHandler()

	def __init__(self):
		self.authenticated = False
		self.user = User(self)
		self.acls = IACLs(self)
		self.processes = Processes(self)
		self.timeout = None
		self.reset_connection_timeout()

	def renew(self):
		CORE.info('Renewing session')

	@tornado.gen.coroutine
	def authenticate(self, request):
		pam = self.__auth.get_handler(request.body_arguments['locale'])
		result = yield pool.submit(self.__auth.authenticate, pam, request.body_arguments)
		pam.end()
		self.authenticated = bool(result)
		if self.authenticated:
			self.user.set_credentials(**result.credentials)
		raise tornado.gen.Return(result)

	def reset_connection_timeout(self):
		self.timeout = SERVER_CONNECTION_TIMEOUT


class Sessions(object):

	sessions = {}

	@classmethod
	def get(cls, session_id):
		return cls.sessions.get(session_id, Session())

	@classmethod
	def put(cls, session_id, session):
		cls.sessions[session_id] = session


class Resource(tornado.web.RequestHandler):

	def get_current_user(self):
		return Sessions.get(self.get_cookie('UMCSessionId'))  # TODO: port

	def prepare(self):
		self._ = self.locale.translate
		self.request.content_negotiation_lang = 'json'
		self.decode_request_arguments()
		self.current_user.reset_connection_timeout()
		# self.check_saml_session_validity()

	@property
	def lo(self):
		return get_machine_connection(write=False)[0]

	@allow_get_request
	def handle_request_unauthorized(self, msg):
		raise Unauthorized(self._('For using this request a login is required.'))

	def load_json(self, body):
		try:
			json_ = json.loads(body)
			if not isinstance(json_, dict):
				raise BadRequest(self._('JSON document have to be dict'))
		except ValueError:
			raise BadRequest(self._('Invalid JSON document'))
		return json_

	def decode_request_arguments(self):
		if self.request.headers.get('Content-Type', '').startswith('application/json'):  # normal (json) request
			# get body and parse json
			body = u'{}'
			if self.request.method in ('POST', 'PUT'):
				if not self.request.headers.get(u"Content-Length"):
					raise HTTPError(LENGTH_REQUIRED, 'Missing Content-Length header')
				body = self.request.body.decode('UTF-8', 'replace')

			args = self.load_json(body)
			if isinstance(args.get('flavor'), type(u'')):
				self.request.headers['X-UMC-Flavor'] = args['flavor']
			self.request.body_arguments = args.get('options', {})
			self.request.body = json.dumps(self.request.body_arguments).encode('ASCII')
#		else:
#			kwargs = dict((name, self.get_query_arguments(name)) for name in self.request.query_arguments)
#			kwargs = dict((name, value[0] if len(value) == 1 else value) for name, value in kwargs.items())
#			# request is not json
#			args = {'options': kwargs}
#			if 'flavor' in kwargs:
#				args['flavor'] = kwargs['flavor']

	def content_negotiation(self, response, wrap=True):
		lang = self.request.content_negotiation_lang
		formatter = getattr(self, '%s_%s' % (self.request.method.lower(), lang), getattr(self, 'get_%s' % (lang,)))
		codec = getattr(self, 'content_negotiation_%s' % (lang,))
		self.finish(codec(formatter(response, wrap)))

	def get_json(self, result, wrap=True):
		message = self._headers.get('X-UMC-Message')
		response = {'status': self.get_status()}  # TODO: get rid of this
		if message:
			response['message'] = message
		if wrap:
			response['result'] = result
		else:
			response.update(result)
		return response

	def content_negotiation_json(self, response):
		self.set_header('Content-Type', 'application/json')
		return json.dumps(response).encode('ASCII')


class NewSession(Resource):

	def get(self):
		session = self.current_user
		session.renew()
		self.content_negotiation(None)


class Auth(Resource):

	def parse_authorization(self):
		return  # do not call super method, prevent basic auth

	@tornado.gen.coroutine
	def get(self):
		#request.body = sanitize_args(DictSanitizer(dict(
		#	username=StringSanitizer(required=True),
		#	password=StringSanitizer(required=True),
		#	auth_type=StringSanitizer(allow_none=True),
		#	new_password=StringSanitizer(required=False, allow_none=True),
		#)), 'request', {'request': request.body})

		try:
			content_length = int(self.request.headers.get("Content-Length", 0))
		except ValueError:
			content_length = None
		if not content_length and content_length != 0:
			CORE.process('auth: missing Content-Length header')
			raise HTTPError(LENGTH_REQUIRED)

		if self.request.method in ('POST', 'PUT'):
			max_length = 2000 * 1024
			if content_length >= max_length:  # prevent some DoS
				raise HTTPError(REQUEST_ENTITY_TOO_LARGE, 'Request data is too large, allowed length is %d' % max_length)

		CORE.info('Reloading resources: UCR, modules, categories')
		ucr.load()
		moduleManager.load()
		categoryManager.load()

		self.request.body_arguments['auth_type'] = None
		self.request.body_arguments['locale'] = self.locale.code
		session = self.current_user
		result = yield session.authenticate(self.request)

		# create a sessionid if the user is not yet authenticated
		sessionid = self.create_sessionid(True)
		self.set_session(sessionid, session.user.username, password=session.user.password)
		Sessions.put(sessionid, session)
		self.set_status(result.status)
		if result.message:
			self.set_header('X-UMC-Message', result.message)
		self.content_negotiation(result.result)

	@tornado.web.asynchronous
	def post(self, *args):
		return self.get(*args)


class Application:

	def __init__(self):
		import tornado
		tornado.locale.load_gettext_translations('/usr/share/locale', 'univention-management-console')
		super(Application, self).__init__([
			(r'/get/ucr', UCR),
			(r'/get/meta', Meta),
			(r'/get/info', Info),
			(r'/get/modules', Modules),
			(r'/get/categories', Categories),
			(r'/get/user/preferences', UserPreferences),
			(r'/get/hosts', Hosts),
			(r'/set/password', SetPassword),
			(r'/set/locale', SetLocale),
			(r'/set/user/preferences', SetUserPreferences),
			(r'/upload/', Upload),
			(r'/upload/(.+)', Command),
			(r'/command/(.+)', Command),
		])


class Modules(Resource):

	def prepare(self):
		super(Modules, self).prepare()
		self.i18n = I18N_Manager()
		self.i18n['umc-core'] = I18N()
		self.i18n.set_locale(self.locale.code)

	@allow_unauthorized
	def get(self):
		categoryManager.load()
		moduleManager.load()
		if self.get_argument('reload', False):
			CORE.info('Reloading ACLs for existing session')
			self.current_user.acls._reload_acls_and_permitted_commands()

		permitted_commands = list(self.current_user.acls.get_permitted_commands(moduleManager).values())

		favorites = self._get_user_favorites()
		modules = [
			self._module_definition(module, favorites)
			for module in permitted_commands
			if not module.flavors
		]
		modules.extend([
			self._flavor_definition(module, flavor, favorites)
			for module in permitted_commands
			for flavor in module.flavors
		])

		CORE.info('Modules: %s' % (modules,))
		self.content_negotiation({'modules': modules}, wrap=False)

	def _flavor_definition(self, module, flavor, favorites):
		favcat = []
		if '%s:%s' % (module.id, flavor.id) in favorites:
			favcat.append('_favorites_')

		translationId = flavor.translationId or module.id
		return {
			'id': module.id,
			'flavor': flavor.id,
			'name': self.i18n._(flavor.name, translationId),
			'url': self.i18n._(module.url, translationId),
			'description': self.i18n._(flavor.description, translationId),
			'icon': flavor.icon,
			'categories': (flavor.categories or (module.categories if not flavor.hidden else [])) + favcat,
			'priority': flavor.priority,
			'keywords': list(set(flavor.keywords + [self.i18n._(keyword, translationId) for keyword in flavor.keywords])),
			'version': flavor.version,
		}

	def _module_definition(self, module, favorites):
		favcat = []
		if module.id in favorites:
			favcat.append('_favorites_')
		translationId = module.translationId or module.id
		return {
			'id': module.id,
			'name': self.i18n._(module.name, translationId),
			'url': self.i18n._(module.url, translationId),
			'description': self.i18n._(module.description, translationId),
			'icon': module.icon,
			'categories': module.categories + favcat,
			'priority': module.priority,
			'keywords': list(set(module.keywords + [self.i18n._(keyword, translationId) for keyword in module.keywords])),
			'version': module.version,
		}

	def _get_user_favorites(self):
		if not self.current_user.user.user_dn:  # user not authenticated or no LDAP user
			return set(ucr.get('umc/web/favorites/default', '').split(','))
		lo = self.current_user.user.get_user_ldap_connection(no_cache=True)
		favorites = self._get_user_preferences(lo).setdefault('favorites', ucr.get('umc/web/favorites/default', '')).strip()
		return set(favorites.split(','))

	def _get_user_preferences(self, lo):
		user_dn = self.current_user.user.user_dn
		if not user_dn or not lo:
			return {}
		try:
			preferences = lo.get(user_dn, ['univentionUMCProperty']).get('univentionUMCProperty', [])
		except (ldap.LDAPError, udm_errors.base) as exc:
			CORE.warn('Failed to retrieve user preferences: %s' % (exc,))
			return {}
		preferences = (val.decode('utf-8', 'replace') for val in preferences)
		return dict(val.split(u'=', 1) if u'=' in val else (val, u'') for val in preferences)

	post = get


class Categories(Resource):

	@allow_unauthorized
	def get(self):
		categoryManager.load()
		ucr.load()
		_ucr_dict = dict(ucr.items())
		categories = []
		for category in categoryManager.values():
			categories.append({
				'id': category.id,
				'icon': category.icon,
				'color': category.color,
				'name': self._(category.name, category.domain).format(**_ucr_dict),
				'priority': category.priority
			})
		CORE.info('Categories: %s' % (categories,))
		self.content_negotiation({'categories': categories}, wrap=False)

	post = get


class SetLocale(Resource):

	@sanitize(locale=StringSanitizer(required=True))
	def handle_request_set_locale(self, locale):
		self.update_language([locale])


class Upload(Resource):

	@allow_get_request
	@sanitize(DictSanitizer(dict(
		tmpfile=StringSanitizer(required=True),
		filename=StringSanitizer(required=True),
		name=StringSanitizer(required=True),
	)))
	def get(self):
		"""Handles an UPLOAD request. The command is used for the HTTP
		access to the UMC server. Incoming HTTP requests that send a
		list of files are passed on to the UMC server by storing the
		files in temporary files and passing the information about the
		files to the UMC server in the options of the request. The
		request options must be a list of dictionaries. Each dictionary
		must contain the following keys:

		* *filename* -- the original name of the file
		* *name* -- name of the form field
		* *tmpfile* -- filename of the temporary file

		:param Request msg: UMCP request
		"""

		result = []
		for file_obj in self.request.body_arguments:
			tmpfilename, filename, name = file_obj['tmpfile'], file_obj['filename'], file_obj['name']

			# limit files to tmpdir
			if not os.path.realpath(tmpfilename).startswith(TEMPUPLOADDIR):
				raise BadRequest('invalid file: invalid path')

			# check if file exists
			if not os.path.isfile(tmpfilename):
				raise BadRequest('invalid file: file does not exists')

			# don't accept files bigger than umc/server/upload/max
			st = os.stat(tmpfilename)
			max_size = int(ucr.get('umc/server/upload/max', 64)) * 1024
			if st.st_size > max_size:
				os.remove(tmpfilename)
				raise BadRequest('filesize is too large, maximum allowed filesize is %d' % (max_size,))

			with open(tmpfilename, 'rb') as buf:
				b64buf = base64.b64encode(buf.read()).decode('ASCII')
			result.append({'filename': filename, 'name': name, 'content': b64buf})

		return result


class IACLs(object):

	def __init__(self, session):
		self.session = session
		self.acls = None
		self.__permitted_commands = None
		self._reload_acls_and_permitted_commands()

	def _reload_acls_and_permitted_commands(self):
		if not self.session.authenticated:
			# We need to set empty ACL's for unauthenticated requests
			self.acls = ACLs()
		else:
			lo, po = get_machine_connection()
			try:
				self.acls = LDAP_ACLs(lo, self.session.user.username, ucr['ldap/base'])
			except (ldap.LDAPError, udm_errors.ldapError):
				reset_ldap_connection_cache(lo)
				raise
		self.__permitted_commands = None
		self.get_permitted_commands(moduleManager)

	def is_command_allowed(self, request, command):
		kwargs = {}
		content_type = request.headers.get('Content-Type', '')
		if content_type.startswith('application/json'):
			kwargs.update(dict(
				options=request.body_arguments,
				flavor=request.headers.get('X-UMC-Flavor'),
			))

		return moduleManager.is_command_allowed(self.acls, command, **kwargs)

	def get_permitted_commands(self, moduleManager):
		if self.__permitted_commands is None:
			# fixes performance leak?
			self.__permitted_commands = moduleManager.permitted_commands(ucr['hostname'], self.acls)
		return self.__permitted_commands

	def get_module_providing(self, moduleManager, command):
		permitted_commands = self.get_permitted_commands(moduleManager)
		module_name = moduleManager.module_providing(permitted_commands, command)

		try:
			# check if the module exists in the module manager
			moduleManager[module_name]
		except KeyError:
			# the module has been removed from moduleManager (probably through a reload)
			CORE.warn('Module %r (command=%r) does not exists anymore' % (module_name, command))
			moduleManager.load()
			self._reload_acls_and_permitted_commands()
			module_name = None
		return module_name

	def get_method_name(self, moduleManager, module_name, command):
		module = self.get_permitted_commands(moduleManager)[module_name]
		methods = (cmd.method for cmd in module.commands if cmd.name == command)
		for method in methods:
			return method


class Command(Resource):

	def error_handling(self, etype, exc, etraceback):
		super(Command, self).error_handling(etype, exc, etraceback)
		# make sure that the UMC login dialog is shown if e.g. restarting the UMC-Server during active sessions
		if isinstance(exc, UMC_Error) and exc.status == 403:
			exc.status = 401

	@tornado.gen.coroutine
	@allow_get_request
	def get(self, command):
		"""Handles a COMMAND request. The request must contain a valid
		and known command that can be accessed by the current user. If
		access to the command is prohibited the request is answered as a
		forbidden command.

		If there is no running module process for the given command a
		new one is started and the request is added to a queue of
		requests that will be passed on when the process is ready.

		If a module process is already running the request is passed on
		and the inactivity timer is reset.
		"""
		session = self.current_user
		acls = session.acls

		module_name = acls.get_module_providing(moduleManager, command)
		module_name = acls.get_module_providing(moduleManager, command)
		if not module_name:
			CORE.warn('No module provides %s' % (command))
			raise Forbidden()

		CORE.info('Checking ACLs for %s (%s)' % (command, module_name))
		if not acls.is_command_allowed(self.request, command):
			CORE.warn('Command %s is not allowed' % (command))
			raise Forbidden()

		methodname = acls.get_method_name(moduleManager, module_name, command)
		if not methodname:
			CORE.warn('Command %s does not exists' % (command))
			raise Forbidden()

		headers = self.get_request_header(session, methodname)

		process = session.processes.get_process(module_name, self.locale.code)
		CORE.info('Passing request to module %s' % (module_name,))

		try:
			yield process.connect()
			# send first command
			response = yield process.request(self.request.method, self.request.full_url(), body=self.request.body or None, headers=headers)
		except CouldNotConnect as exc:
			# (happens during starting the service and subprocesses when the UNIX sockets aren't available yet)
			# cleanup module
			session.processes.stop_process(module_name)
			# TODO: read stderr
			raise BadGateway('%s: %s: %s' % (self._('Connection to module process failed'), module_name, exc))
		else:
			CORE.process('Recevied response %s' % (response.code,))
			self.set_status(response.code, response.reason)
			self._headers = tornado.httputil.HTTPHeaders()

			for header, v in response.headers.get_all():
				if header.title() not in ('Content-Length', 'Transfer-Encoding', 'Content-Encoding', 'Connection', 'X-Http-Reason', 'Range', 'Trailer', 'Server', 'Set-Cookie'):
					self.add_header(header, v)

			if response.body:
				self.set_header('Content-Length', len(response.body))
				self.write(response.body)
			self.finish()

	def get_request_header(self, session, methodname):
		headers = dict(self.request.headers)
		for header in ('Content-Length', 'Transfer-Encoding', 'Content-Encoding', 'Connection', 'X-Http-Reason', 'Range', 'Trailer', 'Server', 'Set-Cookie'):
			headers.pop(header, None)
		headers['X-User-Dn'] = session.user.user_dn
		#headers['X-UMC-Flavor'] = None
		# Forwarded=client.ip
		headers['Authorization'] = 'basic ' + base64.b64encode('%s:%s' % (session.user.username, session.user.password)).decode('ASCII')
		headers['X-UMC-Method'] = methodname
		#headers['X-UMC-SAML'] = None
		return headers

	@tornado.web.asynchronous
	def post(self, *args):
		return self.get(*args)

	@tornado.web.asynchronous
	def put(self, *args):
		return self.get(*args)

	@tornado.web.asynchronous
	def delete(self, *args):
		return self.get(*args)

	@tornado.web.asynchronous
	def patch(self, *args):
		return self.get(*args)

	@tornado.web.asynchronous
	def options(self, *args):
		return self.get(*args)


class Processes(object):

	def __init__(self, session):
		self.session = session
		self.__processes = {}

	def get_process(self, module_name, accepted_language):
		if module_name not in self.__processes:
			CORE.info('Starting new module process %s' % (module_name,))
			try:
				mod_proc = ModuleProcess(module_name, debug=MODULE_DEBUG_LEVEL, locale=accepted_language)
			except EnvironmentError as exc:
				message = self._('Could not open the module. %s Please try again later.') % {
					errno.ENOMEM: self._('There is not enough memory available on the server.'),
					errno.EMFILE: self._('There are too many opened files on the server.'),
					errno.ENFILE: self._('There are too many opened files on the server.'),
					errno.ENOSPC: self._('There is not enough free space on the server.'),
					errno.ENOENT: self._('The executable was not found.'),
				}.get(exc.errno, self._('An unknown operating system error occurred (%s).' % (exc,)))
				raise ServiceUnavailable(message)
			self.__processes[module_name] = mod_proc

		return self.__processes[module_name]

	def stop_process(self, module_name):
		proc = self.__processes.pop(module_name, None)
		if proc:
			proc.stop()

	def has_active_module_processes(self):
		return self.__processes

	def update_module_passwords(self):
		user = self.session.user
		if self.__processes:
			CORE.process('Updating user password in %d running module processes (auth-type: %s).' % (len(self.__processes), user.auth_type))
		for module_name, proc in self.__processes.items():
			CORE.info('Update the users password in the running %r module instance.' % (module_name,))
			req = Request('SET', arguments=[module_name], options={'password': user.password, 'auth_type': user.auth_type})
			try:
				proc.request(req)
			except Exception:
				CORE.error(traceback.format_exc())


class Exit(Resource):

	def get(self, module_name):
		"""Handles an EXIT request. If the request does not have an
		argument that contains a valid name of a running UMC module
		instance the request is returned as a bad request.

		If the request is valid it is passed on to the module
		process. Additionally a timer of 3000 milliseconds is
		started. After that amount of time the module process MUST have
		been exited itself. If not the UMC server will kill the module
		process.

		:param Request msg: UMCP request
		"""
		if module_name in self.__processes:
			self.__processes[module_name].request(msg)
			CORE.info('Ask module %s to shutdown gracefully' % module_name)
			# added timer to kill away module after 3000ms
			cb = notifier.Callback(self._purge_child, module_name)
			self.__processes[module_name].__killtimer = notifier.timer_add(3000, cb)
		else:
			CORE.info('Got EXIT request for a non-existing module %s' % module_name)
		self.content_negotiation(None)

	def _purge_child(self, module_name):
		if module_name in self.__processes:
			CORE.process('module %s is still running - purging module out of memory' % module_name)
			pid = self.__processes[module_name].pid()
			try:
				os.kill(pid, 9)
			except OSError as exc:
				CORE.warn('Failed to kill module %s: %s' % (module_name, exc))
		return False

	def shutdown(self):
		"""Instructs the module process to shutdown"""
		if self.__processes:
			CORE.info('The session is shutting down. Sending EXIT request to %d modules.' % len(self.__processes))

		for module_name in list(self.__processes.keys()):
			CORE.info('Ask module %s to shutdown gracefully' % (module_name,))
			req = Request('EXIT', arguments=[module_name, 'internal'])
			process = self.__processes.pop(module_name)
			process.request(req)
			notifier.timer_remove(process._connect_timer)
			notifier.timer_add(4000, process.stop)

		if self._user_connections:
			reset_ldap_connection_cache(*self._user_connections)

		if isinstance(self.acls, LDAP_ACLs):
			reset_ldap_connection_cache(self.acls.lo)
			self.acls = None


class UCR(Resource):

	#@sanitize(StringSanitizer(required=True))
	def get(self):
		ucr.load()
		result = {}
		for value in self.request.body_arguments:
			if value.endswith('*'):
				value = value[:-1]
				result.update(dict((x, ucr.get(x)) for x in ucr.keys() if x.startswith(value)))
			else:
				result[value] = ucr.get(value)
		self.content_negotiation(result)

	def post(self):
		return self.get()


class Meta(Resource):

	META_JSON_PATH = '/var/www/univention/meta.json'

	META_UCR_VARS = [
		'domainname',
		'hostname',
		'ldap/master',
		'license/base',
		'server/role',
		'ssl/validity/host',
		'ssl/validity/root',
		'ssl/validity/warning',
		'umc/web/favorites/default',
		'umc/web/piwik',
		'update/available',
		'update/reboot/required',
		'uuid/license',
		'uuid/system',
		'version/erratalevel',
		'version/patchlevel',
		'version/releasename',
		'version/version',
	]

	@allow_unauthorized
	def get(self):
		def _get_ucs_version():
			try:
				return '{version/version}-{version/patchlevel} errata{version/erratalevel} ({version/releasename})'.format(**ucr)
			except KeyError:
				pass

		def _has_system_uuid():
			fake_uuid = '00000000-0000-0000-0000-000000000000'
			return ucr.get('uuid/system', fake_uuid) != fake_uuid

		def _has_free_license():
			return ucr.get('license/base') in ('UCS Core Edition', 'Free for personal use edition')

		try:
			with open(self.META_JSON_PATH) as fd:
				meta_data = json.load(fd)
		except (EnvironmentError, ValueError) as exc:
			CORE.error('meta.json is not available: %s' % (exc,))
			meta_data = {}

		if not self.current_user.authenticated:
			return meta_data

		ucr.load()
		meta_data.update(dict(
			ucsVersion=_get_ucs_version(),
			ucs_version=_get_ucs_version(),
			has_system_uuid=_has_system_uuid(),
			has_free_license=_has_free_license(),
			hasFreeLicense=_has_free_license(),
			has_license_base=bool(ucr.get('license/base')),
			appliance_name=ucr.get('umc/web/appliance/name'),
		))
		meta_data.update([(i, ucr.get(i)) for i in self.META_UCR_VARS])
		self.content_negotiation(meta_data)


class Info(Resource):

	CHANGELOG_VERSION = re.compile(r'^[^(]*\(([^)]*)\).*')

	def get_umc_version(self):
		try:
			with gzip.open('/usr/share/doc/univention-management-console-server/changelog.Debian.gz') as fd:
				line = fd.readline().decode('utf-8', 'replace')
		except IOError:
			return
		try:
			return self.CHANGELOG_VERSION.match(line).groups()[0]
		except AttributeError:
			return

	def get_ucs_version(self):
		return '{0}-{1} errata{2} ({3})'.format(ucr.get('version/version', ''), ucr.get('version/patchlevel', ''), ucr.get('version/erratalevel', '0'), ucr.get('version/releasename', ''))

	def get(self):
		ucr.load()

		result = {
			'umc_version': self.get_umc_version(),
			'ucs_version': self.get_ucs_version(),
			'server': '{0}.{1}'.format(ucr.get('hostname', ''), ucr.get('domainname', '')),
			'ssl_validity_host': int(ucr.get('ssl/validity/host', '0')) * 24 * 60 * 60 * 1000,
			'ssl_validity_root': int(ucr.get('ssl/validity/root', '0')) * 24 * 60 * 60 * 1000,
		}
		self.content_negotiation(result)


class Hosts(Resource):

	def get(self):
		self.content_negotiation(self.get_hosts())

	def get_hosts(self):
		lo = self.lo
		if not lo:  # unjoined / no LDAP connection
			return []
		try:
			domaincontrollers = lo.search(filter="(objectClass=univentionDomainController)", attr=['cn', 'associatedDomain'])
		except (ldap.LDAPError, udm_errors.base) as exc:
			reset_ldap_connection_cache(lo)
			CORE.warn('Could not search for domaincontrollers: %s' % (exc))
			return []

		return sorted(
			b'.'.join((computer['cn'][0], computer['associatedDomain'][0])).decode('utf-8', 'replace')
			for dn, computer in domaincontrollers
			if computer.get('associatedDomain')
		)


class SetPassword(Resource):

	@sanitize(password=DictSanitizer(dict(
		password=StringSanitizer(required=True),
		new_password=StringSanitizer(required=True),
	)))
	def post(self, request):
		username = self.username
		password = request.options['password']['password']
		new_password = request.options['password']['new_password']

		CORE.info('Changing password of user %r' % (username,))
		pam = PamAuth(str(self.i18n.locale))
		change_password = notifier.Callback(pam.change_password, username, password, new_password)
		password_changed = notifier.Callback(self._password_changed, request, new_password)
		thread = threads.Simple('change_password', change_password, password_changed)
		thread.run()

	def _password_changed(self, thread, result, request, new_password):
		# it is important that this thread callback must not raise an exception. Otherwise the UMC-Server crashes.
		if isinstance(result, PasswordChangeFailed):
			self.finished(request.id, {'new_password': '%s' % (result,)}, message=str(result), status=400)  # 422
		elif isinstance(result, BaseException):
			self.thread_finished_callback(thread, result, request)
		else:
			CORE.info('Successfully changed password')
			self.content_negotiation(None)
			self.set_header('X-UMC-Message', self._('Password successfully changed.'))
			self.auth_type = None
			self._password = new_password
			self.current_user.processes.update_module_passwords()


class UserPreferences(Resource):

	def get(self):
		# fallback is an empty dict
		lo = self.current_user.user.get_user_ldap_connection()
		result = {'preferences': self._get_user_preferences(lo)}
		self.content_negotiation(result)

	def _get_user_preferences(self, lo):
		user_dn = self.current_user.user.user_dn
		if not user_dn or not lo:
			return {}
		try:
			preferences = lo.get(user_dn, ['univentionUMCProperty']).get('univentionUMCProperty', [])
		except (ldap.LDAPError, udm_errors.base) as exc:
			CORE.warn('Failed to retrieve user preferences: %s' % (exc,))
			return {}
		preferences = (val.decode('utf-8', 'replace') for val in preferences)
		return dict(val.split(u'=', 1) if u'=' in val else (val, u'') for val in preferences)


class SetUserPreferences(UserPreferences):

	def get(self):
		return self.post()

	#@sanitize(user=DictSanitizer(dict(
	#	preferences=DictSanitizer(dict(), required=True),
	#)))
	def post(self):
		lo = self.current_user.user.get_user_ldap_connection()
		# eliminate double entries
		preferences = self._get_user_preferences(lo)
		preferences.update(dict(self.request.body_arguments['preferences']))
		if preferences:
			self._set_user_preferences(lo, preferences)
		self.content_negotiation(None)

	def _set_user_preferences(self, lo, preferences):
		user_dn = self.current_user.user.user_dn
		if not user_dn or not lo:
			return

		user = lo.get(user_dn, ['univentionUMCProperty', 'objectClass'])
		old_preferences = user.get('univentionUMCProperty')
		object_classes = list(set(user.get('objectClass', [])) | set([b'univentionPerson']))

		# validity / sanitizing
		new_preferences = []
		for key, value in preferences.items():
			if not isinstance(key, six.string_types):
				CORE.warn('user preferences keys needs to be strings: %r' % (key,))
				continue

			# we can put strings directly into the dict
			if isinstance(value, six.string_types):
				new_preferences.append((key, value))
			else:
				new_preferences.append((key, json.dumps(value)))
		new_preferences = [b'%s=%s' % (key.encode('utf-8'), value.encode('utf-8')) for key, value in new_preferences]

		lo.modify(user_dn, [['univentionUMCProperty', old_preferences, new_preferences], ['objectClass', user.get('objectClass', []), object_classes]])
