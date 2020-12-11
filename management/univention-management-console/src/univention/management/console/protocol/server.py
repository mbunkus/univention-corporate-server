#!/usr/bin/python
# -*- coding: utf-8 -*-
#
# Univention Management Console
#  UMC web server
#
# Copyright 2011-2020 Univention GmbH
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

from __future__ import division

import os
import re
import sys
import time
import uuid
import json
import zlib
import base64
import signal
import hashlib
import logging
import resource
import tempfile
import binascii
import datetime
import traceback
import functools
import threading
from argparse import ArgumentParser
from six.moves.urllib_parse import urlparse, urlunsplit, quote
from six.moves.http_client import REQUEST_ENTITY_TOO_LARGE, LENGTH_REQUIRED, NOT_FOUND, BAD_REQUEST, UNAUTHORIZED, SERVICE_UNAVAILABLE

import six
import notifier
from ipaddress import ip_address
from cherrypy.lib.httputil import valid_status
from tornado.web import RequestHandler, Application as TApplication, HTTPError
from tornado.httpserver import HTTPServer
import tornado
from concurrent.futures import ThreadPoolExecutor
from multiprocessing import Manager

import univention.debug as ud
from univention.management.console.protocol import Request, TEMPUPLOADDIR
from univention.management.console.log import CORE, log_init, log_reopen
from univention.management.console.config import ucr, get_int
from univention.management.console.protocol.session import Auth, Upload, Command, UCR, Meta, Info, Modules, Categories, UserPreferences, Hosts, SetPassword, SetLocale, SetUserPreferences

from saml2 import BINDING_HTTP_POST, BINDING_HTTP_ARTIFACT, BINDING_HTTP_REDIRECT
from saml2.client import Saml2Client
from saml2.metadata import create_metadata_string
from saml2.response import VerificationError, UnsolicitedResponse, StatusError
from saml2.s_utils import UnknownPrincipal, UnsupportedBinding, rndstr
from saml2.sigver import MissingKey, SignatureError
from saml2.ident import code as encode_name_id, decode as decode_name_id

from univention.lib.i18n import NullTranslation

try:
	from html import escape, unescape
except ImportError:  # Python 2
	import HTMLParser
	html_parser = HTMLParser.HTMLParser()
	unescape = html_parser.unescape
	from cgi import escape

try:
	from time import monotonic
except ImportError:
	from monotonic import monotonic


_ = NullTranslation('univention-management-console-frontend').translate

_session_timeout = get_int('umc/http/session/timeout', 300)

REQUEST_ENTITY_TOO_LARGE, LENGTH_REQUIRED, NOT_FOUND, BAD_REQUEST, UNAUTHORIZED, SERVICE_UNAVAILABLE = int(REQUEST_ENTITY_TOO_LARGE), int(LENGTH_REQUIRED), int(NOT_FOUND), int(BAD_REQUEST), int(UNAUTHORIZED), int(SERVICE_UNAVAILABLE)

pool = ThreadPoolExecutor(max_workers=get_int('umc/http/maxthreads', 35))

if 422 not in tornado.httputil.responses:
	tornado.httputil.responses[422] = 'Unprocessable Entity'  # Python 2 is missing this status code

m = Manager()


def SharedMemoryDict(*args, **kwargs):
	return m.dict(*args, **kwargs)


class NotFound(HTTPError):

	def __init__(self):
		super(NotFound, self).__init__(404)


class UMCP_Dispatcher(object):

	"""Dispatcher used to exchange the requests between CherryPy and UMC"""
	sessions = {}
#
#		# bind session to IP
#		if queuerequest.ip != client.ip and not (queuerequest.ip in ('127.0.0.1', '::1') and client.ip in ('127.0.0.1', '::1')):
#			CORE.warn('The sessionid (ip=%s) is not valid for this IP address (%s)' % (client.ip, queuerequest.ip))
#			response = Response(queuerequest.request)
#			response.status = UNAUTHORIZED
#			response.message = 'The current session is not valid with your IP address for security reasons. This might happen after switching the network. Please login again.'
#			# very important! We must expire the session cookie, with the same path, otherwise one ends up in a infinite redirection loop after changing the IP address (e.g. because switching from VPN to regular network)
#			for name in queuerequest.request.cookies:
#				if name.startswith('UMCSessionId'):
#					response.cookies[name] = {
#						'expires': datetime.datetime.fromtimestamp(0),
#						'path': '/univention/',
#						'version': 1,
#						'value': '',
#					}
#			queuerequest.response_queue.put(response)
#			return


class UploadManager(dict):

	def add(self, request_id, store):
		with tempfile.NamedTemporaryFile(prefix=request_id, dir=TEMPUPLOADDIR, delete=False) as tmpfile:
			tmpfile.write(store['body'])
		self.setdefault(request_id, []).append(tmpfile.name)

		return tmpfile.name

	def cleanup(self, request_id):
		if request_id in self:
			filenames = self[request_id]
			for filename in filenames:
				if os.path.isfile(filename):
					os.unlink(filename)
			del self[request_id]
			return True

		return False


_upload_manager = UploadManager()


class User(object):

	__slots__ = ('sessionid', 'username', 'password', 'saml', '_timeout', '_timeout_id')

	def __init__(self, sessionid, username, password, saml=None):
		self.sessionid = sessionid
		self.username = username
		self.password = password
		self.saml = saml
		self._timeout_id = None
		self.reset_timeout()

	def _session_timeout_timer(self):
		session = UMCP_Dispatcher.sessions.get(self.sessionid)
		if session and session._requestid2response_queue:
			self._timeout = 1
			self._timeout_id = notifier.timer_add(1000, self._session_timeout_timer)
			return

		CORE.info('session %r timed out' % (self.sessionid,))
		Ressource.sessions.pop(self.sessionid, None)
		self.on_logout()
		return False

	def reset_timeout(self):
		self.disconnect_timer()
		self._timeout = monotonic() + _session_timeout
		self._timeout_id = notifier.timer_add(int(self.session_end_time - monotonic()) * 1000, self._session_timeout_timer)

	def disconnect_timer(self):
		notifier.timer_remove(self._timeout_id)

	def timed_out(self, now):
		return self.session_end_time < now

	@property
	def session_end_time(self):
		if self.is_saml_user() and self.saml.session_end_time:
			return self.saml.session_end_time
		return self._timeout

	def is_saml_user(self):
		# self.saml indicates that it was originally a
		# saml user. but it may have upgraded and got a
		# real password. the saml user object is still there,
		# though
		return self.password is None and self.saml

	def on_logout(self):
		self.disconnect_timer()
		if SAMLBase.SP and self.saml:
			try:
				SAMLBase.SP.local_logout(decode_name_id(self.saml.name_id))
			except Exception as exc:  # e.g. bsddb.DBNotFoundError
				CORE.warn('Could not remove SAML session: %s' % (exc,))

	def get_umc_password(self):
		if self.is_saml_user():
			return self.saml.message
		else:
			return self.password

	def get_umc_auth_type(self):
		if self.is_saml_user():
			return "SAML"
		else:
			return None

	def __repr__(self):
		return '<User(%s, %s, %s)>' % (self.username, self.sessionid, self.saml is not None)


class SAMLUser(object):

	__slots__ = ('message', 'username', 'session_end_time', 'name_id')

	def __init__(self, response, message):
		self.name_id = encode_name_id(response.name_id)
		self.message = message
		self.username = u''.join(response.ava['uid'])
		self.session_end_time = 0
		if response.not_on_or_after:
			self.session_end_time = int(monotonic() + (response.not_on_or_after - time.time()))


traceback_pattern = re.compile(r'(Traceback.*most recent call|File.*line.*in.*\d)')


class UMC_HTTPError(HTTPError):

	""" HTTPError which sets an error result """

	def __init__(self, status=500, message=None, body=None, error=None, reason=None):
		HTTPError.__init__(self, status, message, reason=reason)
		self.body = body
		self.error = error


class SamlError(HTTPError):

	def __init__(self, _=_):
		self._ = _

	def error(func=None, status=400):  # noqa: N805
		def _decorator(func):
			def _decorated(self, *args, **kwargs):
				message = func(self, *args, **kwargs) or ()
				super(SamlError, self).__init__(status, message)
				if "Passive authentication not supported." not in message:
					# "Passive authentication not supported." just means an active login is required. That is expected and needs no logging. It still needs to be raised though.
					CORE.warn('SamlError: %s %s' % (status, message))
				return self
			return _decorated
		if func is None:
			return _decorator
		return _decorator(func)

	def from_exception(self, etype, exc, etraceback):
		if isinstance(exc, UnknownPrincipal):
			return self.unknown_principal(exc)
		if isinstance(exc, UnsupportedBinding):
			return self.unsupported_binding(exc)
		if isinstance(exc, VerificationError):
			return self.verification_error(exc)
		if isinstance(exc, UnsolicitedResponse):
			return self.unsolicited_response(exc)
		if isinstance(exc, StatusError):
			return self.status_error(exc)
		if isinstance(exc, MissingKey):
			return self.missing_key(exc)
		if isinstance(exc, SignatureError):
			return self.signature_error(exc)
		six.reraise(etype, exc, etraceback)

	@error
	def unknown_principal(self, exc):
		return self._('The principal is unknown: %s') % (exc,)

	@error
	def unsupported_binding(self, exc):
		return self._('The requested SAML binding is not known: %s') % (exc,)

	@error
	def unknown_logout_binding(self, binding):
		return self._('The logout binding is not known.')

	@error
	def verification_error(self, exc):
		return self._('The SAML response could not be verified: %s') % (exc,)

	@error
	def unsolicited_response(self, exc):
		return self._('Received an unsolicited SAML response. Please try to single sign on again by accessing /univention/saml/. Error message: %s') % (exc,)

	@error
	def status_error(self, exc):
		return self._('The identity provider reported a status error: %s') % (exc,)

	@error(status=500)
	def missing_key(self, exc):
		return self._('The issuer %r is now known to the SAML service provider. This is probably a misconfiguration and might be resolved by restarting the univention-management-console-server.') % (str(exc),)

	@error
	def signature_error(self, exc):
		return self._('The SAML response contained a invalid signature: %s') % (exc,)

	@error
	def unparsed_saml_response(self):
		return self._("The SAML message is invalid for this service provider.")

	@error(status=500)
	def no_identity_provider(self):
		return self._('There is a configuration error in the service provider: No identity provider are set up for use.')

	@error  # TODO: multiple choices redirection status
	def multiple_identity_provider(self, idps, idp_query_param):
		return self._('Could not pick an identity provider. You can specify one via the query string parameter %(param)r from %(idps)r') % {'param': idp_query_param, 'idps': idps}


class Application(TApplication):

	def __init__(self, **kwargs):
		tornado.locale.load_gettext_translations('/usr/share/locale', 'univention-management-console')
		super(Application, self).__init__([
			(r'/auth/sso', AuthSSO),
			(r'/auth/?', Auth),
			(r'/upload/', Upload),
			(r'/upload/(.+)', Command),
			(r'/command/(.+)', Command),
			(r'/get/session-info', SessionInfo),
			(r'/get/ip-address', GetIPAdress),
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
			(r'/saml/', SamlACS),
			(r'/saml/metadata', SamlMetadata),
			(r'/saml/slo/?', SamlSingleLogout),
			(r'/saml/logout', SamlLogout),
			(r'/saml/iframe/?', SamlIframeACS),
			(r'/', Index),
			(r'/logout', Logout),
		], default_handler_class=Nothing, **kwargs)

		SamlACS.reload()


class Resource(RequestHandler):

	def set_default_headers(self):
		self.set_header('Server', 'UMC-Server/1.0')  # TODO:

	def prepare(self):
		self._proxy_uri()
		self.parse_authorization()

	def _proxy_uri(self):
		if self.request.headers.get('X-UMC-HTTPS') == 'on':
			self.request.protocol = 'https'
		self.request.uri = '/univention%s' % (self.request.uri,)

	def parse_authorization(self):
		credentials = self.request.headers.get('Authorization')
		if not credentials:
			return
		sessionid = self.create_sessionid(False)
		if sessionid in UMCP_Dispatcher.sessions:
			return
		try:
			scheme, credentials = credentials.split(u' ', 1)
		except ValueError:
			raise HTTPError(400)
		if scheme.lower() != u'basic':
			return
		try:
			username, password = base64.b64decode(credentials.encode('utf-8')).decode('latin-1').split(u':', 1)
		except ValueError:
			raise HTTPError(400)

		# authenticate
		sessionid = self.sessionidhash()
		req = Request('AUTH')
		req.body = {
			"username": username,
			"password": password
		}
		self._auth_request(req, sessionid)

	def _auth_request(self, req, sessionid):
		response = self.make_queue_request(sessionid, req)

		self._x_log(99, 'auth: creating session with sessionid=%r' % (sessionid,))
		CORE.process('auth_type=%r' % (req.body.get('auth_type'),))

		username = req.body.get('username')
		password = req.body.get('password')
		body = response.body
		if response.mimetype == 'application/json':
			username = body.get('result', {}).get('username', username)
			body = json.dumps(response.body).encode('UTF-8')
		self.set_session(sessionid, username, password=password)
		return body

	def get_ip_address(self):
		"""get the IP address of client by last entry (from apache) in X-FORWARDED-FOR header"""
		return self.request.headers.get('X-Forwarded-For', self.request.remote_ip).rsplit(', ', 1).pop()

	def sessionidhash(self):
		session = u'%s%s%s%s' % (self.request.headers.get('Authorization', ''), self.request.headers.get('Accept-Language', ''), self.get_ip_address(), self.sessionidhash.salt)
		return hashlib.sha256(session.encode('UTF-8')).hexdigest()[:36]
		# TODO: the following is more secure (real random) but also much slower
		return binascii.hexlify(hashlib.pbkdf2_hmac('sha256', session, self.sessionidhash.salt, 100000))[:36]

	sessionidhash.salt = rndstr()

	def write_error(self, status_code, exc_info=None, **kwargs):
		if exc_info and isinstance(exc_info[1], HTTPError):
			exc = exc_info[1]
			traceback = None
			body = None
			if isinstance(exc, UMC_HTTPError) and self.settings.get("serve_traceback") and isinstance(exc.error, dict) and exc.error.get('traceback'):
				traceback = '%s\nRequest: %s\n\n%s' % (exc.log_message, exc.error.get('command'), exc.error.get('traceback'))
				traceback = traceback.strip()
				body = exc.body
			content = self.default_error_page(exc.status_code, exc.log_message, traceback, body)
			self.finish(content.encode('utf-8'))
			return

		if exc_info:
			kwargs['exc_info'] = exc_info
		super(Resource, self).write_error(status_code, **kwargs)

	def default_error_page(self, status, message, traceback, result=None):
		if message and not traceback and traceback_pattern.search(message):
			index = message.find('Traceback') if 'Traceback' in message else message.find('File')
			message, traceback = message[:index].strip(), message[index:].strip()
		if traceback:
			CORE.error('%s' % (traceback,))
		if ucr.is_false('umc/http/show_tracebacks', False):
			traceback = None

		accept_json, accept_html = 0, 0
		for mimetype, qvalue in self.check_acceptable('Accept', 'text/html'):
			if mimetype in ('text/*', 'text/html'):
				accept_html = max(accept_html, qvalue)
			if mimetype in ('application/*', 'application/json'):
				accept_json = max(accept_json, qvalue)
		if accept_json < accept_html:
			return self.default_error_page_html(status, message, traceback, result)
		page = self.default_error_page_json(status, message, traceback, result)
		if self.request.headers.get('X-Iframe-Response'):
			self.set_header('Content-Type', 'text/html')
			return '<html><body><textarea>%s</textarea></body></html>' % (escape(page, False),)
		return page

	def default_error_page_html(self, status, message, traceback, result=None):
		content = self.default_error_page_json(status, message, traceback, result)
		try:
			with open('/usr/share/univention-management-console-frontend/error.html', 'r') as fd:
				content = fd.read().replace('%ERROR%', json.dumps(escape(content, True)))
			self.set_header('Content-Type', 'text/html; charset=UTF-8')
		except (OSError, IOError):
			pass
		return content

	def default_error_page_json(self, status, message, traceback, result=None):
		""" The default error page for UMCP responses """
		status, _, description = valid_status(status)
		if status == 401 and message == description:
			message = ''
		location = self.request.full_url().rsplit('/', 1)[0]
		if status == 404:
			traceback = None
		response = {
			'status': status,
			'message': message,
			'traceback': unescape(traceback) if traceback else traceback,
			'location': location,
		}
		if result:
			response['result'] = result
		self.set_header('Content-Type', 'application/json')
		return json.dumps(response)

	def check_acceptable(self, header, default=''):
		accept = self.request.headers.get(header, default).split(',')
		langs = []
		for language in accept:
			if not language.strip():
				continue
			score = 1.0
			parts = language.strip().split(";")
			for part in (x for x in parts[1:] if x.strip().startswith("q=")):
				try:
					score = float(part.strip()[2:])
					break
				except (ValueError, TypeError):
					raise
					score = 0.0
			langs.append((parts[0].strip(), score))
		langs.sort(key=lambda pair: pair[1], reverse=True)
		return langs

	_logOptions = {
		'error': CORE.error,
		'warn': CORE.warn,
		'info': CORE.info,
	}

	sessions = SharedMemoryDict()

	@property
	def name(self):
		"""returns class name"""
		return self.__class__.__name__

	def _x_log(self, loglevel, _msg):
		port = self.request.connection.context.address[1]
		msg = '%s (%s:%s) %s' % (self.name, self.get_ip_address(), port, _msg)
		self._logOptions.get(loglevel, lambda x: ud.debug(ud.MAIN, loglevel, x))(msg)

	def suffixed_cookie_name(self, name):
		host, _, port = self.request.headers.get('Host', '').partition(':')
		if port:
			try:
				port = '-%d' % (int(port),)
			except ValueError:
				port = ''
		return '%s%s' % (name, port)

	def create_sessionid(self, random=True):
		if self.get_session():
			# if the user is already authenticated at the UMC-Server
			# we must not change the session ID cookie as this might cause
			# race conditions in the frontend during login, especially when logged in via SAML
			return self.get_session_id()
		user = self.get_user()
		if user:
			# If the user was already authenticated at the UMC-Server
			# and the connection was lost (e.g. due to a module timeout)
			# we must not change the session ID cookie, as there might be multiple concurrent
			# requests from the same client during a new initialization of the connection to the UMC-Server.
			# They must cause that the session has one singleton connection!
			return user.sessionid
		if random:
			return str(uuid.uuid4())
		return self.sessionidhash()

	def get_session_id(self):
		"""get the current session ID from cookie (or basic auth hash)."""
		# caution: use this function wisely: do not create a new session with this ID!
		# because it is an arbitrary value coming from the Client!
		return self.get_cookie('UMCSessionId') or self.sessionidhash()

	def get_session(self):
		return UMCP_Dispatcher.sessions.get(self.get_session_id())

	def check_saml_session_validity(self):
		user = self.get_user()
		if user and user.saml is not None and user.timed_out(monotonic()):
			raise HTTPError(UNAUTHORIZED)

	def set_cookies(self, *cookies, **kwargs):
		# TODO: use expiration from session timeout?
		# set the cookie once during successful authentication
		# force expiration of cookie in 5 years from now on...
		# IE does not support max-age
		expires = kwargs.get('expires') or (datetime.datetime.now() + datetime.timedelta(days=5 * 365))
		for name, value in cookies:
			name = self.suffixed_cookie_name(name)
			self.set_cookie(name, value, expires=expires, path='/univention/', version=1)

	def get_cookie(self, name):
		cookie = self.request.cookies.get
		morsel = cookie(self.suffixed_cookie_name(name)) or cookie(name)
		if morsel:
			return morsel.value

	def set_session(self, sessionid, username, password=None, saml=None):
		olduser = self.get_user()

		if olduser:
			olduser.disconnect_timer()
		user = User(sessionid, username, password, saml or olduser and olduser.saml)

		self.sessions[sessionid] = user
		self.set_cookies(('UMCSessionId', sessionid), ('UMCUsername', username))
		return user

	def expire_session(self):
		sessionid = self.get_session_id()
		if sessionid:
			user = self.sessions.pop(sessionid, None)
			if user:
				user.on_logout()
			UMCP_Dispatcher.cleanup_session(sessionid)
			self.set_cookies(('UMCSessionId', ''), expires=datetime.datetime.fromtimestamp(0))

	def get_user(self):
		value = self.get_session_id()
		if not value or value not in self.sessions:
			return
		user = self.sessions[value]
		if user.timed_out(monotonic()):
			return
		return user


def json_response(func):
	@functools.wraps(func)
	def decorator(self):
		result = func(self)
		self.set_header('Content-Type', 'application/json')
		self.finish(json.dumps(result).encode('ASCII'))
	return decorator


class Index(Resource):

	def get(self):
		self.redirect('/univention/', status=305)

	def post(self, path):
		return self.get(path)


class Logout(Resource):

	def get(self, **kwargs):
		user = self.get_user()
		if user and user.saml is not None:
			return self.redirect('/univention/saml/logout', status=303)
		self.expire_session()
		self.redirect(ucr.get('umc/logout/location') or '/univention/', status=303)

	def post(self, path):
		return self.get(path)


class Nothing(Resource):

	def prepare(self, *args, **kwargs):
		super(Nothing, self).prepare(*args, **kwargs)
		raise NotFound()


class SessionInfo(Resource):

	@json_response
	def get(self):
		info = {}
		user = self.get_user()
		if user is None:
			raise HTTPError(UNAUTHORIZED)
		info['username'] = user.username
		info['auth_type'] = user.saml and 'SAML'
		info['remaining'] = int(user.session_end_time - monotonic())
		return {"status": 200, "result": info, "message": ""}

	def post(self):
		return self.get()


class GetIPAdress(Resource):

	@json_response
	def get(self):
		try:
			addresses = self.addresses
		except ValueError:
			# hacking attempt
			addresses = [self.request.remote_ip]
		return addresses

	@property
	def addresses(self):
		addresses = self.request.headers.get('X-Forwarded-For', self.request.remote_ip).split(',') + [self.request.remote_ip]
		addresses = set(ip_address(x.decode('ASCII', 'ignore').strip() if isinstance(x, bytes) else x.strip()) for x in addresses)
		addresses.discard(ip_address(u'::1'))
		addresses.discard(ip_address(u'127.0.0.1'))
		return tuple(address.exploded for address in addresses)

	def post(self, path):
		return self.get(path)


class CPCommand(Resource):

	def post(self, path):
		return self.get(path)

	def get_request(self, path, args):
		if self._is_file_upload():
			return self.get_request_upload(path, args)

		if not path:
			raise HTTPError(NOT_FOUND)

		req = Request('COMMAND', [path], options=args.get('options', {}))
		if 'flavor' in args:
			req.flavor = args['flavor']

		return req

	def get_response(self, sessionid, path, args):
		response = super(CPCommand, self).get_response(sessionid, path, args)

		# check if the request is a iframe upload
		if 'X-Iframe-Response' in self.request.headers:
			# this is a workaround to make iframe uploads work, they need the textarea field
			self.set_header('Content-Type', 'text/html')
			return '<html><body><textarea>%s</textarea></body></html>' % (response)

		return response

	def get_request_upload(self, path, args):
		self._x_log('info', 'Handle upload command')
		self.request.headers['Accept'] = 'application/json'  # enforce JSON response in case of errors
		if args.get('options', {}).get('iframe', False) not in ('false', False, 0, '0'):
			self.request.headers['X-Iframe-Response'] = 'true'  # enforce textarea wrapping
		req = Request('UPLOAD', arguments=[path or ''])
		req.body = self._get_upload_arguments(req)
		return req

	def _is_file_upload(self):
		return self.request.headers.get('Content-Type', '').startswith('multipart/form-data')

	def _get_upload_arguments(self, req):
		options = []
		body = {}

		# check if enough free space is available
		min_size = get_int('umc/server/upload/min_free_space', 51200)  # kilobyte
		s = os.statvfs(TEMPUPLOADDIR)
		free_disk_space = s.f_bavail * s.f_frsize // 1024  # kilobyte
		if free_disk_space < min_size:
			self._x_log('error', 'there is not enough free space to upload files')
			raise HTTPError(BAD_REQUEST, 'There is not enough free space on disk')

		for name, field in self.request.files.items():
			for part in field:
				tmpfile = _upload_manager.add(req.id, part)
				options.append(self._sanitize_file(tmpfile, name, part))

		for name in self.request.body_arguments:
			value = self.get_body_arguments(name)
			if len(value) == 1:
				value = value[0]
			body[name] = value

		body['options'] = options
		return body

	def _sanitize_file(self, tmpfile, name, store):
		# check if filesize is allowed
		st = os.stat(tmpfile)
		max_size = get_int('umc/server/upload/max', 64) * 1024
		if st.st_size > max_size:
			self._x_log('warn', 'file of size %d could not be uploaded' % (st.st_size))
			raise HTTPError(BAD_REQUEST, 'The size of the uploaded file is too large')

		filename = store['filename']
		# some security
		for c in '<>/':
			filename = filename.replace(c, '_')

		return {
			'filename': filename,
			'name': name,
			'tmpfile': tmpfile,
			'content_type': store['content_type'],
		}


class AuthSSO(Resource):

	def parse_authorization(self):
		return  # do not call super method, prevent basic auth

	def get(self):
		self._x_log('info', '/auth/sso: got new auth request')

		user = self.get_user()
		if not user or not user.saml or user.timed_out(monotonic()):
			# redirect user to login page in case he's not authenticated or his session timed out
			self.redirect('/univention/saml/', status=303)
			return

		req = Request('AUTH')
		req.body = {
			"auth_type": "SAML",
			"username": user.username,
			"password": user.saml.message
		}

		try:
			self._auth_request(req, user.sessionid)
		except UMC_HTTPError as exc:
			if exc.status == UNAUTHORIZED:
				# slapd down, time synchronization between IDP and SP is wrong, etc.
				CORE.error('SAML authentication failed: Make sure slapd runs and the time on the service provider and identity provider is identical.')
				raise HTTPError(
					500,
					'The SAML authentication failed. This might be a temporary problem. Please login again.\n'
					'Further information can be found in the following logfiles:\n'
					'* /var/log/univention/management-console-web-server.log\n'
					'* /var/log/univention/management-console-server.log\n'
				)
			raise

		# protect against javascript:alert('XSS'), mailto:foo and other non relative links!
		location = urlparse(self.get_query_argument('return', '/univention/management/'))
		if location.path.startswith('//'):
			location = urlparse('')
		location = urlunsplit(('', '', location.path, location.query, location.fragment))
		self.redirect(location, status=303)

	def post(self):
		return self.get()


class SAMLBase(Resource):

	SP = None
	identity_cache = '/var/cache/univention-management-console/saml.bdb'
	state_cache = SharedMemoryDict()  # None
	configfile = '/usr/share/univention-management-console/saml/sp.py'
	idp_query_param = "IdpQuery"
	bindings = [BINDING_HTTP_REDIRECT, BINDING_HTTP_POST, BINDING_HTTP_ARTIFACT]
	outstanding_queries = {}


class SamlMetadata(SAMLBase):

	def get(self):
		metadata = create_metadata_string(self.configfile, None, valid='4', cert=None, keyfile=None, mid=None, name=None, sign=False)
		self.set_header('Content-Type', 'application/xml')
		self.finish(metadata)


class SamlACS(SAMLBase):

	@property
	def sp(self):
		if not self.SP and not self.reload():
			raise HTTPError(SERVICE_UNAVAILABLE, 'Single sign on is not available due to misconfiguration. See logfiles.')
		return self.SP

	@classmethod
	def reload(cls):
		CORE.info('Reloading SAML service provider configuration')
		sys.modules.pop(os.path.splitext(os.path.basename(cls.configfile))[0], None)
		try:
			cls.SP = Saml2Client(config_file=cls.configfile, identity_cache=cls.identity_cache, state_cache=cls.state_cache)
			return True
		except Exception:
			CORE.warn('Startup of SAML2.0 service provider failed:\n%s' % (traceback.format_exc(),))
		return False

	def get(self):
		binding, message, relay_state = self._get_saml_message()

		if message is None:
			return self.do_single_sign_on(relay_state=self.get_query_argument('location', '/univention/management/'))

		acs = self.attribute_consuming_service
		if relay_state == 'iframe-passive':
			acs = self.attribute_consuming_service_iframe
		acs(binding, message, relay_state)

	def post(self):
		return self.get()

	def attribute_consuming_service(self, binding, message, relay_state):
		response = self.acs(message, binding)
		saml = SAMLUser(response, message)
		self.set_session(self.create_sessionid(), saml.username, saml=saml)
		# protect against javascript:alert('XSS'), mailto:foo and other non relative links!
		location = urlparse(relay_state)
		if location.path.startswith('//'):
			location = urlparse('')
		location = urlunsplit(('', '', location.path, location.query, location.fragment))
		self.redirect(location, status=303)

	def attribute_consuming_service_iframe(self, binding, message, relay_state):
		self.request.headers['Accept'] = 'application/json'  # enforce JSON response in case of errors
		self.request.headers['X-Iframe-Response'] = 'true'  # enforce textarea wrapping
		response = self.acs(message, binding)
		saml = SAMLUser(response, message)
		sessionid = self.create_sessionid()
		self.set_session(sessionid, saml.username, saml=saml)
		self.set_header('Content-Type', 'text/html')
		data = {"status": 200, "result": {"username": saml.username}}
		self.finish(b'<html><body><textarea>%s</textarea></body></html>' % (json.dumps(data).encode('ASCII'),))

	def _logout_success(self):
		user = self.get_user()
		if user:
			user.saml = None
		self.redirect('/univention/logout', status=303)

	def _get_saml_message(self):
		"""Get the SAML message and corresponding binding from the HTTP request"""
		if self.request.method not in ('GET', 'POST'):
			self.set_header('Allow', 'GET, HEAD, POST')
			raise HTTPError(405)

		if self.request.method == 'GET':
			binding = BINDING_HTTP_REDIRECT
			args = self.request.query_arguments
		elif self.request.method == "POST":
			binding = BINDING_HTTP_POST
			args = self.request.body_arguments

		relay_state = args.get('RelayState', [''])[0]
		try:
			message = args['SAMLResponse'][0]
		except KeyError:
			try:
				message = args['SAMLRequest'][0]
			except KeyError:
				try:
					message = args['SAMLart'][0]
				except KeyError:
					return None, None, None
				message = self.sp.artifact2message(message, 'spsso')
				binding = BINDING_HTTP_ARTIFACT

		return binding, message, relay_state

	def acs(self, message, binding):  # attribute consuming service  # TODO: rename into parse
		try:
			response = self.sp.parse_authn_request_response(message, binding, self.outstanding_queries)
		except (UnknownPrincipal, UnsupportedBinding, VerificationError, UnsolicitedResponse, StatusError, MissingKey, SignatureError):
			raise SamlError().from_exception(*sys.exc_info())
		if response is None:
			raise SamlError().unparsed_saml_response()
		self.outstanding_queries.pop(response.in_response_to, None)
		return response

	def do_single_sign_on(self, **kwargs):
		binding, http_args = self.create_authn_request(**kwargs)
		self.http_response(binding, http_args)

	def create_authn_request(self, **kwargs):
		"""Creates the SAML <AuthnRequest> request and returns the SAML binding and HTTP response.

			Returns (binding, http-arguments)
		"""
		identity_provider_entity_id = self.select_identity_provider()
		binding, destination = self.get_identity_provider_destination(identity_provider_entity_id)

		relay_state = kwargs.pop('relay_state', None)

		reply_binding, service_provider_url = self.select_service_provider()
		sid, message = self.sp.create_authn_request(destination, binding=reply_binding, assertion_consumer_service_urls=(service_provider_url,), **kwargs)

		http_args = self.sp.apply_binding(binding, message, destination, relay_state=relay_state)
		self.outstanding_queries[sid] = service_provider_url  # self.request.full_url()  # TODO: shouldn't this contain service_provider_url?
		return binding, http_args

	def select_identity_provider(self):
		"""Select an identity provider based on the available identity providers.
			If multiple IDP's are set up the client might have specified one in the query string.
			Otherwise an error is raised where the user can choose one.

			Returns the EntityID of the IDP.
		"""
		idps = self.sp.metadata.with_descriptor("idpsso")
		if not idps and self.reload():
			idps = self.sp.metadata.with_descriptor("idpsso")
		if self.get_query_argument(self.idp_query_param, None) in idps:
			return self.get_query_argument(self.idp_query_param)
		if len(idps) == 1:
			return list(idps.keys())[0]
		if not idps:
			raise SamlError().no_identity_provider()
		raise SamlError().multiple_identity_provider(list(idps.keys()), self.idp_query_param)

	def get_identity_provider_destination(self, entity_id):
		"""Get the destination (with SAML binding) of the specified entity_id.

			Returns (binding, destination-URI)
		"""
		return self.sp.pick_binding("single_sign_on_service", self.bindings, "idpsso", entity_id=entity_id)

	def select_service_provider(self):
		"""Select the ACS-URI and binding of this service provider based on the request uri.
			Tries to preserve the current scheme (HTTP/HTTPS) and netloc (host/IP) but falls back to FQDN if it is not set up.

			Returns (binding, service-provider-URI)
		"""
		acs = self.sp.config.getattr("endpoints", "sp")["assertion_consumer_service"]
		service_url, reply_binding = acs[0]
		netloc = False
		p2 = urlparse(self.request.full_url())
		for _url, _binding in acs:
			p1 = urlparse(_url)
			if p1.scheme == p2.scheme and p1.netloc == p2.netloc:
				netloc = True
				service_url, reply_binding = _url, _binding
				if p1.path == p2.path:
					break
			elif not netloc and p1.netloc == p2.netloc:
				service_url, reply_binding = _url, _binding
		CORE.info('SAML: picked %r for %r with binding %r' % (service_url, self.request.full_url(), reply_binding))
		return reply_binding, service_url

	def http_response(self, binding, http_args):
		"""Converts the HTTP arguments from pysaml2 into the tornado response."""
		body = u''.join(http_args["data"])
		for key, value in http_args["headers"]:
			self.set_header(key, value)

		if binding in (BINDING_HTTP_ARTIFACT, BINDING_HTTP_REDIRECT):
			self.set_status(303 if self.request.supports_http_1_1() and self.request.method == 'POST' else 302)
			if not body:
				self.redirect(self._headers['Location'], status=self.get_status())
				return

		self.finish(body.encode('UTF-8'))


class SamlSingleLogout(SamlACS):

	def get(self, *args, **kwargs):  # single logout service
		binding, message, relay_state = self._get_saml_message()
		if message is None:
			raise HTTPError(400, 'The HTTP request is missing required SAML parameter.')

		try:
			is_logout_request = b'LogoutRequest' in zlib.decompress(base64.b64decode(message.encode('UTF-8')), -15).split(b'>', 1)[0]
		except Exception:
			CORE.error(traceback.format_exc())
			is_logout_request = False

		if is_logout_request:
			user = self.get_user()
			if not user or user.saml is None:
				# The user is either already logged out or has no cookie because he signed in via IP and gets redirected to the FQDN
				name_id = None
			else:
				name_id = user.saml.name_id
				user.saml = None
			http_args = self.sp.handle_logout_request(message, name_id, binding, relay_state=relay_state)
			self.http_response(binding, http_args)
			return
		else:
			response = self.sp.parse_logout_request_response(message, binding)
			self.sp.handle_logout_response(response)
		self._logout_success()


class SamlLogout(SamlACS):

	def get(self):
		user = self.get_user()

		if user is None or user.saml is None:
			return self._logout_success()

		# What if more than one
		try:
			data = self.sp.global_logout(user.saml.name_id)
		except KeyError:
			try:
				tb = sys.exc_info()[2]
				while tb.tb_next:
					tb = tb.tb_next
				if tb.tb_frame.f_code.co_name != 'entities':
					raise
			finally:
				tb = None
			# already logged out or UMC-Webserver restart
			user.saml = None
			data = {}

		for entity_id, logout_info in data.items():
			if not isinstance(logout_info, tuple):
				continue  # result from logout, should be OK

			binding, http_args = logout_info
			if binding not in (BINDING_HTTP_POST, BINDING_HTTP_REDIRECT):
				raise SamlError().unknown_logout_binding(binding)

			self.http_response(binding, http_args)
			return
		self._logout_success()


class SamlIframeACS(SamlACS):

	def get(self):
		self.do_single_sign_on(is_passive='true', relay_state='iframe-passive')


class Server(object):

	def __init__(self):
		self.parser = ArgumentParser()
		self.parser.add_argument(
			'-d', '--debug', type=int, default=get_int('umc/server/debug/level', 1),
			help='if given than debugging is activated and set to the specified level [default: %(default)s]'
		)
		self.parser.add_argument(
			'-L', '--log-file', default='management-console-web-server',
			help='specifies an alternative log file [default: %(default)s]'
		)
		self.parser.add_argument(
			'-c', '--processes', default=get_int('umc/http/processes', 1), type=int,
			help='How many processes to start'
		)
		self.options = self.parser.parse_args()

		# cleanup environment
		os.environ.clear()
		os.environ['PATH'] = '/bin:/sbin:/usr/bin:/usr/sbin'

		# init logging
		if True or not self.options.daemon_mode:
			log_init('/dev/stderr', self.options.debug, self.options.processes > 1)
		else:
			log_init(self.options.log_file, self.options.debug, self.options.processes > 1)

		os.umask(0o077)

	def signal_handler_hup(self, signo, frame):
		"""Handler for the reload action"""
		ucr.load()
		log_reopen()
		print(''.join(['%s:\n%s' % (th, ''.join(traceback.format_stack(sys._current_frames()[th.ident]))) for th in threading.enumerate()]))

	def signal_handler_reload(self, signo, frame):
		log_reopen()
		SamlACS.reload()

	def run(self):
		signal.signal(signal.SIGHUP, self.signal_handler_hup)
		signal.signal(signal.SIGUSR1, self.signal_handler_reload)

		try:
			fd_limit = get_int('umc/http/max-open-file-descriptors', 65535)
			resource.setrlimit(resource.RLIMIT_NOFILE, (fd_limit, fd_limit))
		except (ValueError, resource.error) as exc:
			CORE.error('Could not raise NOFILE resource limits: %s' % (exc,))

		application = Application(serve_traceback=ucr.is_true('umc/http/show_tracebacks', True))
		server = HTTPServer(
			application,
			idle_connection_timeout=get_int('umc/http/response-timeout', 310),  # is this correct? should be internal response timeout
			max_body_size=get_int('umc/http/max_request_body_size', 104857600),
		)
		server.bind(get_int('umc/http/port', 8090), ucr.get('umc/http/interface', '127.0.0.1'), backlog=get_int('umc/http/requestqueuesize', 100))  # backlog=SERVER_MAX_CONNECTIONS
		server.start(self.options.cpus)

		channel = logging.StreamHandler()
		channel.setFormatter(tornado.log.LogFormatter(fmt='%(color)s%(asctime)s  %(levelname)10s      (%(process)9d) :%(end_color)s %(message)s', datefmt='%d.%m.%y %H:%M:%S'))
		logger = logging.getLogger()
		logger.setLevel(logging.INFO)
		logger.addHandler(channel)

		notifier.init(notifier.GENERIC)
		notifier.dispatch.MIN_TIMER = get_int('umc/http/dispatch-interval', notifier.dispatch.MIN_TIMER)
		notifier.dispatcher_add(UMCP_Dispatcher.check_queue)
		running = True

		def loop():
			while running:
				notifier.step()
		#nf_thread = threading.Thread(target=loop, name='notifier')
		#nf_thread.start()
		pool.submit(loop)
		ioloop = tornado.ioloop.IOLoop.current()

		try:
			ioloop.start()
		except Exception:
			CORE.error(traceback.format_exc())
			ioloop.stop()
			pool.shutdown(False)
			raise
		except (KeyboardInterrupt, SystemExit):
			ioloop.stop()
			pool.shutdown(False)
		finally:
			running = False


if __name__ == '__main__':
	Server().run()
