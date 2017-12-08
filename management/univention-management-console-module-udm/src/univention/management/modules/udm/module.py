#!/usr/bin/python2.7
# -*- coding: utf-8 -*-
#
# Univention Management Console
#  Univention Directory Manager Module
#
# Copyright 2017-2019 Univention GmbH
#
# http://www.univention.de/
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
# <http://www.gnu.org/licenses/>.

import os
import json
import copy
import urllib
import base64
import binascii
from urlparse import urljoin, urlparse, urlunparse
from urllib import quote
import argparse

import tornado.ioloop
from tornado.web import Application, RequestHandler, HTTPError
from tornado.concurrent import run_on_executor
import tornado.gen
from concurrent.futures import ThreadPoolExecutor

from ldap.filter import filter_format
import xml.etree.cElementTree as ET

from univention.management.console.config import ucr
from univention.management.console.ldap import get_user_connection, get_machine_connection
from univention.management.console.modules.udm.udm_ldap import get_module, set_bind_function, UDM_Module, ldap_dn2path, read_syntax_choices, _get_syntax, container_modules, UDM_Error
from univention.management.console.modules.udm.udm_ldap import SuperordinateDoesNotExist, NoIpLeft
from univention.management.console.modules.udm.tools import check_license, LicenseError
import univention.directory.reports as udr
import univention.admin.uexceptions as udm_errors
import univention.admin.modules as udm_modules
from univention.lib.i18n import Translation
# TODO: PAM authentication ?
# TODO: use http link header
# TODO: set Last-Modified
# FIXME: add_asterisks sanitizer
# FIXME: prevent in the javascript UMC module that navigation container query is called with container=='None'
# TODO: translation
# FIXME: it seems request.path contains the un-urlencoded path, could be security issue!

_ = Translation('univention-management-console-module-udm').translate

MAX_WORKERS = 35


class NotFound(HTTPError):

	def __init__(self, object_type, dn=None):
		super(NotFound, self).__init__(404, None, '%r %r' % (object_type, dn or ''))  # FIXME: create error message


class Ressource(RequestHandler):

	pool = ThreadPoolExecutor(max_workers=MAX_WORKERS)

	def force_authorization(self):
		self.set_header('WWW-Authenticate', 'Basic realm="Univention Management Console"')
		self.set_status(401)
		self.finish()

	def prepare(self):
		self.request.path_decoded = urllib.unquote(self.request.path)
		authorization = self.request.headers.get('Authorization')
		if not authorization:
			return self.force_authorization()

		try:
			if not authorization.lower().startswith('basic '):
				raise ValueError()
			username, password = base64.decodestring(authorization.split(' ', 1)[1]).split(':', 1)
		except (ValueError, IndexError, binascii.Error):
			raise HTTPError(400)

		# TODO: caching
		lo, po = get_machine_connection()
		try:
			userdn = lo.searchDn(filter_format('(&(objectClass=person)(uid=%s))', [username]), unique=True)[0]
			self.ldap_connection, self.ldap_position = get_user_connection(bind=lambda lo: lo.bind(userdn, password))
			set_bind_function(lambda lo: lo.bind(userdn, password))
			self.request.user_dn = userdn
		except:
			return self.force_authorization()

		self.request.content_negotiation_lang = self.check_acceptable()
		self.decode_request_arguments()

	def get_module(self, object_type):
		module = UDM_Module(object_type)
		if not module or not module.module:
			raise NotFound(object_type)
		return module

	def get_object(self, object_type, dn):
		module = self.get_module(object_type)
		obj = module.get(dn)
		if not obj:
			raise NotFound(object_type, dn)
		return obj

	def check_acceptable(self):
		accept = self.request.headers.get('Accept', 'text/html').split(',')
		langs = []
		for language in accept:
			score = 1.0
			parts = language.strip().split(";")
			for part in (x for x in parts[1:] if x.startswith("q=")):
				try:
					score = float(part)
					break
				except (ValueError, TypeError):
					score = 0.0
			langs.append((parts[0].strip(), score))
		langs.sort(key=lambda pair: pair[1], reverse=True)
		lang = None
		for name, q in langs:
			if name in ('text/html', 'text/xml', 'application/xml', 'text/*', '*/*'):
				lang = 'html'
				break
			elif name in ('application/json', 'application/*'):
				lang = 'json'
				break
		if not lang:
			raise HTTPError(406)
		return lang

	def decode_request_arguments(self):
		if self.request.headers.get('Content-Type', '').startswith('application/json'):
			self.request.body_arguments = json.loads(self.request.body)

	def get_body_argument(self, name, *args):
		if self.request.headers.get('Content-Type', '').startswith('application/json'):
			return self.request.body_arguments.get(name)
		return super(Ressource, self).get_body_argument(name, *args)

	def get_body_arguments(self, name, *args):
		if self.request.headers.get('Content-Type', '').startswith('application/json'):
			return self.request.body_arguments.get(name)
		return super(Ressource, self).get_body_arguments(name, *args)

	def content_negotiation(self, response):
		# TODO: implement XML
		lang = self.request.content_negotiation_lang
		formatter = getattr(self, '%s_%s' % (self.request.method.lower(), lang), getattr(self, 'get_%s' % (lang,)))
		codec = getattr(self, 'content_negotiation_%s' % (lang,))
		self.finish(codec(formatter(response)))

	def content_negotiation_json(self, response):
		self.set_header('Content-Type', 'application/json')
		return json.dumps(response)

	def content_negotiation_html(self, response):
		self.set_header('Content-Type', 'text/html')

		root = ET.Element("html")
		head = ET.SubElement(root, "head")
		ET.SubElement(head, "title", name="blah").text = "Test"
		body = ET.SubElement(root, "body")
		for link in self._headers.get_list('Link'):
			link, foo, _params = link.partition(';')
			link = link.strip().lstrip('<').rstrip('>')
			params = {}
			if _params.strip():
				params = dict((x.strip(), y.strip().strip('"')) for x, y in ((param.split('=', 1) + [''])[:2] for param in _params.split(';')))
			ET.SubElement(head, "link", href=link, **params)
			ET.SubElement(body, "a", href=link, **params).text = params.get('title', link) or link
			ET.SubElement(body, "br")

		if isinstance(response, (list, tuple)):
			body.extend(response)
		elif response is not None:
			body.append(response)

		self.write('<!DOCTYPE html>\n')
		tree = ET.ElementTree(root)
		tree.write(self)

	def get_json(self, response):
		return response

	def get_html(self, response):
		root = []
		if isinstance(response, (list, tuple)):
			for thing in response:
				if isinstance(thing, dict) and thing.get('$url$'):
					x = thing.copy()
					a = ET.Element("a", href=x.pop('$url$'), rel="/udm/relation/object")
					a.text = json.dumps(x, indent=4)
					root.append(a)
					root.append(ET.Element("br"))
				else:
					pre = ET.Element("pre")
					pre.text = json.dumps(thing, indent=4)
					root.append(pre)
					root.append(ET.Element("br"))
		else:
			pre = ET.Element("pre")
			pre.text = json.dumps(response, indent=4)
			root.append(pre)
		return root

	def urljoin(self, *args):
		base = urlparse(self.request.full_url())
		return urljoin(urljoin(urlunparse((base.scheme, base.netloc, 'univention/' if self.request.headers.get('X-Forwarded-Host') else '/', '', '', '')), self.request.path_decoded.lstrip('/')), *args)


class Favicon(Ressource):

	def get(self):
		return


class Relations(Ressource):

	def get(self, relation):
		relations = {
			# IANA:
			'search': 'Refers to a resource that can be used to search through the link\'s context and related resources.',
			'create-form': 'The target IRI points to a resource where a submission form can be obtained.',
			'edit': 'Refers to a resource that can be used to edit the link\'s context.',
			'edit-form': 'The target IRI points to a resource where a submission form for editing associated resource can be obtained.',
			'first': 'An IRI that refers to the furthest preceding resource in a series of resources.',
			'help': 'Refers to context-sensitive help.',
			'index': 'Refers to an index.',
			'item': 'The target IRI points to a resource that is a member of the collection represented by the context IRI.',
			'last': 'An IRI that refers to the furthest following resource in a series of resources.',
			'latest-version': 'Points to a resource containing the latest (e.g., current) version of the context.',
			'next': 'Indicates that the link\'s context is a part of a series, and that the next in the series is the link target. ',
			'original': 'The Target IRI points to an Original Resource.',
			'prev': 'Indicates that the link\'s context is a part of a series, and that the previous in the series is the link target. ',
			'preview': 'Refers to a resource that provides a preview of the link\'s context.',
			'previous': 'Refers to the previous resource in an ordered series of resources. Synonym for "prev".',
			'self': 'Conveys an identifier for the link\'s context. ',
			'start': 'Refers to the first resource in a collection of resources.',
			'type': 'Refers to a resource identifying the abstract semantic type of which the link\'s context is considered to be an instance.',
			'up': 'Refers to a parent document in a hierarchy of documents.',
			'icon': 'Refers to an icon representing the link\'s context.',
			# Univention:
			'object': '',
			'object-modules': '',
			'object-types': 'list of object types matching the given flavor or container',
			'properties': 'properties of the given object type',
			'options': 'options specified for the given object type',
			'layout': 'layout information for the given object type',
			'templates': 'list of template objects for the given object type',
			'containers': 'list of default containers for the given object type',
			'policies': 'list of policy types that apply to the given object type',  # virtual policy object containing the values that the given object or container inherits
			'report-types': 'list of reports for the given object type',
			'default-search': 'default search pattern/value for the given object property',
			'next-free-ip': 'next IP configuration based on the given network object',
			'property-choices': 'determine valid values for a given syntax class',
		}
		result = relations.get(relation)
		self.content_negotiation(result)


class Modules(Ressource):

	mapping = {
		'users': 'users/user',
		'computers': 'computers/computer',
		'groups': 'groups/group',
		'networks': 'networks/network',
		'dhcp': 'dhcp/dhcp',
		'dns': 'dns/dns',
		'shares': 'shares/share',
		'printers': 'shares/print',
		'mail': 'mails/mail',
		'nagios': 'nagios/nagios',
		'policies': 'policies/policy',
		'self': 'users/self',
		#'directory': 'navigation',
	}

	def get(self):
		for main_type in self.mapping:
			self.add_header('Link', '<%s/>; rel="/udm/relation/object-modules"; name="%s"; title=""' % (self.urljoin(quote(main_type)), main_type,))
			# TODO: add license-import
		self.content_negotiation("Hello, world")


class ObjectTypes(Ressource):
	"""get the object types of a specific flavor"""

	def get(self, module_type):
		"""Returns the list of object types matching the given flavor or container.

		requests.options = {}
			'superordinate' -- if available only types for the given superordinate are returned (not for the navigation)
			'container' -- if available only types suitable for the given container are returned (only for the navigation)
		"""
		object_type = Modules.mapping.get(module_type)
		if not object_type:
			raise NotFound(object_type)

		superordinate = self.get_query_argument('superordinate', None)
		module = UDM_Module(object_type)
		if superordinate:
			module = get_module(object_type, superordinate, self.ldap_connection) or module  # FIXME: the object_type param is wrong?!

		result = module.child_modules or []
		if not result:
			result.append({'id': module.name, 'label': module.title})

		for mod in result:
			self.add_header('Link', '<%s/>; rel="/udm/relation/object-types"; name="%s"; title="%s"' % (self.urljoin('../%s' % quote(mod['id'])), mod['id'], mod['label']))
		self.content_negotiation(result)


class ObjectTypesNavigation(Ressource):

	def get(self):
		superordinate = self.get_query_argument('superordinate', None)
		container = self.get_query_argument('container', None) or superordinate
		if not container:
			# no container is specified, return all existing object types
			result = [{
				'id': module[0],
				'label': getattr(module[1], 'short_description', module[0])
			} for module in udm_modules.modules.items()]
			for mod in result:
				self.add_header('Link', '<%s/>; rel="/udm/relation/object-types"; name="%s"; title="%s"' % (self.urljoin(quote(mod['id'])), mod['id'], mod['label']))
			self.content_negotiation(result)
			return

		if 'None' == container:
			# if 'None' is given, use the LDAP base
			container = ucr.get('ldap/base')

		# create a list of modules that can be created
		# ... all container types except container/dc
		allowed_modules = set([m for m in udm_modules.containers if udm_modules.name(m) != 'container/dc'])

		# the container may be a superordinate or have one as its parent
		# (or grandparent, ....)
		superordinate = udm_modules.find_superordinate(container, None, self.ldap_connection)
		if superordinate:
			# there is a superordinate... add its subtypes to the list of allowed modules
			allowed_modules.update(udm_modules.subordinates(superordinate))
		else:
			# add all types that do not have a superordinate
			allowed_modules.update(mod for mod in udm_modules.modules.values() if not udm_modules.superordinates(mod))

		# make sure that the object type can be created
		allowed_modules = [mod for mod in allowed_modules if udm_modules.supports(mod, 'add')]

		# return the final list of object types
		result = [{
			'id': udm_modules.name(module),
			'label': getattr(module, 'short_description', udm_modules.name(module))
		} for module in allowed_modules]
		for mod in result:
			self.add_header('Link', '<%s/>; rel="/udm/relation/object-types"; name="%s"; title="%s"' % (self.urljoin(quote(mod['id'])), mod['id'], mod['label']))
		self.content_negotiation(result)


class ContainerQueryBase(Ressource):

	@tornado.gen.coroutine
	def _container_query(self, object_type, container, modules, scope):
		"""Get a list of containers or child objects of the specified container."""

		if not container:
			container = ucr['ldap/base']
			defaults = {}
			if object_type != 'navigation':
				defaults['$operations$'] = ['search', ],  # disallow edit
			if object_type in ('dns/dns', 'dhcp/dhcp'):
				defaults.update({
					'label': UDM_Module(object_type).title,
					'icon': 'udm-%s' % (object_type.replace('/', '-'),),
				})
			raise tornado.gen.Return([dict({
				'id': container,
				'label': ldap_dn2path(container),
				'icon': 'udm-container-dc',
				'path': ldap_dn2path(container),
				'objectType': 'container/dc',
				'$operations$': UDM_Module('container/dc').operations,
				'$flags$': [],
				'$childs$': True,
				'$isSuperordinate$': False,
			}, **defaults)])

		result = []
		for xmodule in modules:
			xmodule = UDM_Module(xmodule)
			superordinate = None
			if xmodule.superordinate_names:
				for module_superordinate in xmodule.superordinate_names:
					try:
						superordinate = UDM_Module(module_superordinate).get(container)
					except UDM_Error:  # the container is not a direct superordinate  # FIXME: get the "real" superordinate; Bug #40885
						continue
				if superordinate is None:
					continue  # superordinate object could not be load -> ignore module
			try:
				items = yield self.pool.submit(xmodule.search, container, scope=scope, superordinate=superordinate)
				for item in items:
					module = UDM_Module(item.module)
					result.append({
						'id': item.dn,
						'label': item[module.identifies],
						'icon': 'udm-%s' % (module.name.replace('/', '-')),
						'path': ldap_dn2path(item.dn),
						'objectType': module.name,
						'$operations$': module.operations,
						'$flags$': item.oldattr.get('univentionObjectFlag', []),
						'$childs$': module.childs,
						'$isSuperordinate$': udm_modules.isSuperordinate(module.module),
					})
			except UDM_Error as exc:
				raise HTTPError(400, None, str(exc))

		raise tornado.gen.Return(result)


class Navigation(ContainerQueryBase):
	"""GET udm/(dns|dhcp|)/navigation/ (the tree content of navigation/DNS/DHCP)"""

	@tornado.gen.coroutine
	def get(self, object_type):
		ldap_base = ucr['ldap/base']
		container = self.get_query_argument('container', None)

		modules = container_modules()
		scope = 'one'
		if not container:
			# get the tree root == the ldap base
			scope = 'base'
		elif object_type != 'navigation' and container and ldap_base.lower() == container.lower():
			# this is the tree root of DNS / DHCP, show all zones / services
			scope = 'sub'
			modules = [object_type]

		containers = yield self._container_query(object_type, container, modules, scope)
		self.content_negotiation(containers)


class MoveDestinations(ContainerQueryBase):

	def get(self, object_type):
		scope = 'one'
		modules = container_modules()
		container = self.get_query_argument('container', None)
		if not container:
			scope = 'base'

		containers = self._container_query(object_type, container, modules, scope)
		self.content_negotiation(containers)


class LicenseRequest(Ressource):

	def post(self):
		pass  # TODO: implement request_new_license()


class LicenseCheck(Ressource):

	def get(self):
		message = None
		try:
			check_license(self.ldap_connection)
		except LicenseError as exc:
			message = str(exc)
		self.content_negotiation(message)


class License(Ressource):

	def get(self):
		pass  # TODO: implement license_info()

	def post(self):
		pass  # TODO: implement license_import()


class Properties(Ressource):
	"""GET udm/users/user/properties (get properties of users/user object type)"""

	def get(self, object_type, dn=None):
		module = self.get_module(object_type)
		module.load(force_reload=True)  # reload for instant extended attributes

		properties = module.get_properties(dn)
		searchable = self.get_query_argument('searchable', False)
		if searchable:
			properties = [prop for prop in properties if prop.get('searchable', False)]

		self.content_negotiation(properties)


class Options(Ressource):
	"""GET udm/users/user/options (get options of users/user object type)"""

	def get(self, object_type):
		"""Returns the options specified for the given object type"""
		result = self.get_module(object_type).options.keys()
		self.content_negotiation(result)


class Layout(Ressource):
	"""GET udm/users/user/$dn/layout (get layout of users/user object type)"""

	def get(self, object_type, dn=None):
		"""Returns the layout information for the given object type."""

		module = self.get_module(object_type)
		module.load(force_reload=True)  # reload for instant extended attributes

		if object_type == 'users/self':
			dn = None

		result = module.get_layout(dn)
		self.content_negotiation(result)


class Templates(Ressource):
	"""GET udm/users/user/templates (get the list of templates of users/user object type)"""

	def get(self, object_type):
		"""Returns the list of template objects for the given object"""

		module = self.get_module(object_type)
		result = []
		if module.template:
			template = UDM_Module(module.template)
			objects = template.search(ucr.get('ldap/base'))
			for obj in objects:
				obj.open()
				result.append({'id': obj.dn, 'label': obj[template.identifies]})

		self.content_negotiation(result)


class Containers(Ressource):
	"""GET udm/users/user/containers (get default containers for users/user)"""

	def get(self, object_type):
		"""Returns the list of default containers for the given object
		type. Therefor the python module and the default object in the
		LDAP directory are searched.
		"""
		module = self.get_module(object_type)
		containers = [{'id': x, 'label': ldap_dn2path(x)} for x in module.get_default_containers()]
		containers.sort(cmp=lambda x, y: cmp(x['label'].lower(), y['label'].lower()))
		return containers

		self.content_negotiation(containers)


class Policies(Ressource):
	"""GET udm/users/user/policies (get the list of policy-types that apply for users/user object type)"""

	def get(self, object_type):
		module = self.get_module(object_type)
		result = module.policies
		self.content_negotiation(result)


class ReportingBase(Ressource):

	def initialize(self):
		self.reports_cfg = udr.Config()


class ReportTypes(ReportingBase):
	"""GET udm/users/user/report-types (get report-types of users/*)"""

	def get(self, object_type):
		"""Returns a list of reports for the given object type"""
		# i18n: translattion for univention-directory-reports
		# _('PDF Document')
		result = [{'id': name, 'label': _(name)} for name in sorted(self.reports_cfg.get_report_names(object_type))]
		self.content_negotiation(result)


class Report(ReportingBase):
	"""GET udm/users/user/report/$report_type?dn=...&dn=... (create a report of users)"""

	@tornado.gen.coroutine
	def get(self, object_type, report_type):
		# TODO: better use only POST because GET is limited in argument length sometimes?
		dns = self.get_query_arguments('dn')
		yield self.create_report(object_type, report_type, dns)

	@tornado.gen.coroutine
	def post(self, object_type, report_type):
		# TODO: 202 accepted with progress?
		dns = self.get_body_arguments('dn')
		yield self.create_report(object_type, report_type, dns)

	@tornado.gen.coroutine
	def create_report(self, object_type, report_type, dns):
		try:
			report_type in self.reports_cfg.get_report_names(object_type)
		except KeyError:
			raise NotFound(report_type)

		report = udr.Report(self.ldap_connection)
		try:
			report_file = yield self.pool.submit(report.create, object_type, report_type, dns)
		except udr.ReportError as exc:
			raise HTTPError(400, None, str(exc))

		with open(report_file) as fd:
			self.set_header('Content-Type', 'text/csv' if report_file.endswith('.csv') else 'application/pdf')
			self.set_header('Content-Disposition', 'attachment; filename="%s"' % (os.path.basename(report_file).replace('\\', '\\\\').replace('"', '\\"')))
			self.finish(fd.read())
		os.remove(report_file)


class NextFreeIpAddress(Ressource):
	"""GET udm/networks/network/$DN/next-ip (get the next free IP in this network)"""

	def get(self, dn):  # TODO: threaded?! (might have caused something in the past in system setup?!)
		"""Returns the next IP configuration based on the given network object

		requests.options = {}
			'networkDN' -- the LDAP DN of the network object
			'increaseCounter' -- if given and set to True, network object counter for IP addresses is increased

		return: {}
		"""
		obj = self.get_object('networks/network', dn)
		try:
			obj.refreshNextIp()
		except udm_errors.nextFreeIp:
			raise NoIpLeft(dn)

		result = {
			'ip': obj['nextIp'],
			'dnsEntryZoneForward': obj['dnsEntryZoneForward'],
			'dhcpEntryZone': obj['dhcpEntryZone'],
			'dnsEntryZoneReverse': obj['dnsEntryZoneReverse']
		}

		self.content_negotiation(result)

		if self.request.get_query_argument('increaseCounter'):
			# increase the next free IP address
			obj.stepIp()
			obj.modify()


class DefaultValue(Ressource):
	"""GET udm/users/user/properties/$property/default (get the default value for the specified property)"""

	def get(self, object_type, property_):
		module = self.get_module(object_type)
		result = module.get_default_values(property_)
		self.content_negotiation(result)


class Objects(Ressource):

	@tornado.gen.coroutine
	def get(self, object_type):
		"""GET udm/users/user/ (nach Benutzern suchen)"""
		module = self.get_module(object_type)
		self.options(object_type)

		# TODO: replace the superordinate concept by container
		superordinate = self.get_query_argument('superordinate', None)

		container = self.get_query_argument('container', None)
		objectProperty = self.get_query_argument('objectProperty', None)
		objectPropertyValue = self.get_query_argument('objectPropertyValue', None)
		scope = self.get_query_argument('scope', 'sub')
		hidden = self.get_query_argument('hidden', False)
		fields = self.get_query_arguments('fields', [])
		fields = (set(fields) | set([objectProperty])) - set(['name', 'None', None, ''])

		if superordinate:
			mod = get_module(superordinate, superordinate, self.ldap_connection)
			if not mod:
				raise SuperordinateDoesNotExist(superordinate)
			superordinate = mod.get(superordinate)
			container = container or superordinate

		result = yield self.pool.submit(module.search, container, objectProperty, objectPropertyValue, superordinate, scope=scope, hidden=hidden)

		entries = []
		for obj in result or []:
			if obj is None:
				continue
			module = get_module(object_type, obj.dn, self.ldap_connection)
			if module is None:
				# This happens when concurrent a object is removed between the module.search() and get_module() call
				# MODULE.warn('LDAP object does not exists %s (flavor: %s). The object is ignored.' % (obj.dn, request.flavor))
				continue

			assert '/' not in obj.dn  # TODO: escape /
			entry = {
				'$dn$': obj.dn,
				'$childs$': module.childs,
				'$flags$': obj.oldattr.get('univentionObjectFlag', []),
				'$operations$': module.operations,
				'objectType': module.name,
				'labelObjectType': module.subtitle,
				'name': module.obj_description(obj),
				'path': ldap_dn2path(obj.dn, include_rdn=False),
				'$url$': self.urljoin(quote(obj.dn)),
			}
			if '$value$' in fields:
				entry['$value$'] = [module.property_description(obj, column['name']) for column in module.columns]
			for field in fields - set(module.password_properties) - set(entry.keys()):
				entry[field] = module.property_description(obj, field)
			entries.append(entry)

		self.content_negotiation(entries)

	@tornado.gen.coroutine
	def post(self, object_type):
		"""POST udm/users/user/ (Benutzer hinzufügen)"""
		module = self.get_module(object_type)
		container = self.get_body_argument('container')
		superordinate = self.get_body_argument('superordinate')
		options = self.get_body_arguments('options')

		obj = module.module.object(None, self.ldap_connection, self.ldap_position)
		obj.open()
		obj.options = options
		properties = dict((prop, self.get_body_arguments(prop)) for prop in dict(obj.items()))

		dn = yield self.pool.submit(module.create, properties, container=container, superordinate=superordinate)
		self.set_header('Location', self.urljoin(quote(dn)))
		self.set_status(201)

	def options(self, object_type):
		self.set_header('Allow', 'GET, POST, OPTIONS')
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin(''), 'search', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('add/'), 'create-form', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('edit/'), 'edit-form', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('favicon'), 'icon', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('properties'), 'udm/relation/properties', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('options'), 'udm/relation/options', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('layout'), 'udm/relation/layout', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('templates'), 'udm/relation/templates', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('containers'), 'udm/relation/containers', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('policies'), 'udm/relation/policies', ''))
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin('report-types'), 'udm/relation/report-types', ''))
#		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.urljoin(''), '', ''))


class Object(Ressource):

	@tornado.gen.coroutine
	def get(self, object_type, dn):
		"""GET udm/users/user/$DN (get all properties/values of the user)"""
		self.add_header('Link', '<%s>; rel="%s"; title="%s"' % (self.request.path, 'self', ''))
		copy = bool(self.get_query_argument('copy', None))  # TODO: move into own ressource

		def _remove_uncopyable_properties(obj):
			if not copy:
				return
			for name, p in obj.descriptions.items():
				if not p.copyable:
					obj.info.pop(name, None)

		if object_type == 'users/self' and not self.ldap_connection.compare_dn(dn, self.request.user_dn):
			raise HTTPError(403)

		module = get_module(object_type, dn, self.ldap_connection)
		if module is None:
			raise NotFound(object_type, dn)

		obj = yield self.pool.submit(module.get, dn)
		if not obj:
			raise NotFound(object_type, dn)

		_remove_uncopyable_properties(obj)
		obj.set_defaults = True
		obj.set_default_values()
		_remove_uncopyable_properties(obj)
		props = {}
		props['properties'] = obj.info
		for passwd in module.password_properties:
			props['properties'].pop(passwd, None)
		if not copy:
			props['$dn$'] = obj.dn
		props['$options$'] = {}
		for opt in module.get_options(udm_object=obj):
			props['$options$'][opt['id']] = opt['value']
		props['$policies$'] = {}
		for policy in obj.policies:
			pol_mod = get_module(None, policy, self.ldap_connection)
			if pol_mod and pol_mod.name:
				props['$policies$'].setdefault(pol_mod.name, []).append(policy)
		props['$labelObjectType$'] = module.title
		props['$flags$'] = obj.oldattr.get('univentionObjectFlag', [])
		props['$operations$'] = module.operations
		props['$references$'] = module.get_references(dn)
		assert '/' not in obj.dn  # TODO: escape /
		props['$url$'] = self.urljoin(quote(obj.dn))
		self.content_negotiation(props)

	@tornado.gen.coroutine
	def put(self, object_type, dn):
		"""PUT udm/users/user/$DN (Benutzer hinzufügen / modifizieren)"""
		module = get_module(object_type, dn, self.ldap_connection)
		if not module:
			raise NotFound(object_type)  # FIXME: create

		yield self.modify(module, None, dn)

	@tornado.gen.coroutine
	def patch(self, object_type, dn):
		module = get_module(object_type, dn, self.ldap_connection)
		if not module:
			raise NotFound(object_type)
		yield self.modify(module, self.request.body_arguments, dn)

	@tornado.gen.coroutine
	def modify(self, module, properties, dn):
		obj = module.module.object(None, self.ldap_connection, self.ldap_position, dn)
		obj.open()
		obj.options = self.get_body_arguments('$options$')
		if properties is None:
			properties = dict((prop, self.get_body_arguments(prop)) for prop in dict(obj.items()))

		valid = all(x['valid'] if isinstance(x['valid'], bool) else all(x['valid']) for x in self._validate(module, properties))
		if not valid:
			raise HTTPError(422)

		try:
			module._map_properties(obj, properties)
			yield self.pool.submit(obj.modify)
		except udm_errors.base as exc:
			UDM_Error(exc).reraise()

	@tornado.gen.coroutine
	def delete(self, object_type, dn):
		"""DELETE udm/users/user/$DN (Benutzer löschen)"""
		module = get_module(object_type, dn, self.ldap_connection)
		if not module:
			raise NotFound(object_type)

		cleanup = bool(self.get_query_argument('cleanup', False))
		recursive = bool(self.get_query_argument('recursive', False))
		yield self.pool.submit(module.remove, dn, cleanup, recursive)

	def options(self, object_type, dn):
		self.set_header('Allow', 'GET, PUT, DELETE, OPTIONS')

	def _validate(self, module, properties):  # (thread)
		"""Validates the correctness of values for properties of the
		given object type. Therefor the syntax definition of the properties is used.

		return: [ { 'property' : <name>, 'valid' : (True|False), 'details' : <message> }, ... ]
		"""

		result = []
		for property_name, value in properties.items():
			# ignore special properties named like $.*$, e.g. $options$
			if property_name.startswith('$') and property_name.endswith('$'):
				continue
			property_obj = module.get_property(property_name)

			if property_obj is None:
				raise HTTPError(400, None, _('Property %s not found') % property_name)

			if not property_obj.multivalue:
				value = value[0]

			# check each element if 'value' is a list
			if isinstance(value, (tuple, list)) and property_obj.multivalue:
				subResults = []
				subDetails = []
				for ival in value:
					try:
						property_obj.syntax.parse(ival)
						subResults.append(True)
						subDetails.append('')
					except (udm_errors.valueInvalidSyntax, udm_errors.valueError, TypeError) as exc:
						subResults.append(False)
						subDetails.append(str(exc))
				result.append({'property': property_name, 'valid': subResults, 'details': subDetails})
			# otherwise we have a single value
			else:
				try:
					property_obj.syntax.parse(value)
					result.append({'property': property_name, 'valid': True})
				except (udm_errors.valueInvalidSyntax, udm_errors.valueError) as exc:
					result.append({'property': property_name, 'valid': False, 'details': str(exc)})
		return result


class ObjectAdd(Ressource):
	pass


class ObjectEdit(Ressource):
	pass


class PropertyChoices(Ressource):
	"""GET udm/users/user/$DN/property/$name/choices (get possible values/choices for that property)"""

	@tornado.gen.coroutine
	def get(self, object_type, dn, property_):
		module = self.get_module(object_type)
		try:
			syntax = module.module.property_descriptions[property_].syntax
		except KeyError:
			raise NotFound(object_type, dn)
		request_body = {'syntax': syntax.name}  # FIXME
		choices = yield self.pool.submit(read_syntax_choices, _get_syntax(syntax.name), request_body, ldap_connection=self.ldap_connection, ldap_position=self.ldap_position)
		self.content_negotiation(choices)


class PolicyTypes(Ressource):
	"""GET udm/users/user/$DN/policies/$policy_type (get the policies of policy-type for the given object)"""

	def get(self, object_type, dn, policy_type):
		"""Returns a list of policy types that apply to the given object type"""
		module = self.get_module(object_type)
		result = module.policies
		self.content_negotiation(result)


class PolicyResult(Ressource):
	"""GET udm/users/user/policies/$policy_type/$dn?container=true...&policy=... (get the possible policies of the policy-type for user objects located at the containter)"""

	@tornado.gen.coroutine
	def get(self, object_type, policy_type, dn):
		infos = yield self._get(object_type, policy_type, dn)
		self.content_negotiation(infos)

	@run_on_executor(executor='pool')
	def _get(self, object_type, policy_type, dn):
		"""Returns a virtual policy object containing the values that
		the given object or container inherits"""

		is_container = bool(self.get_query_argument('container', None))
		policy_dn = self.get_query_argument('policy', None)

		if is_container:
			# editing a new (i.e. non existing) object -> use the parent container
			obj = self.get_object(get_module(None, dn, self.ldap_connection).module, dn)
		else:
			# editing an exiting UDM object -> use the object itself
			obj = self.get_object(object_type, dn)

		if policy_dn:
			policy_obj = self.get_object(policy_type, policy_dn)
		else:
			policy_obj = self.get_module(policy_type).get(None)
		policy_obj.clone(obj)

		# There are 2x2x2 (=8) cases that may occur (c.f., Bug #31916):
		# (1)
		#   [edit] editing existing UDM object
		#   -> the existing UDM object itself is loaded
		#   [new]  virtually edit non-existing UDM object (when a new object is being created)
		#   -> the parent container UDM object is loaded
		# (2)
		#   [w/pol]   UDM object has assigend policies in LDAP directory
		#   [w/o_pol] UDM object has no policies assigend in LDAP directory
		# (3)
		#   [inherit] user request to (virtually) change the policy to 'inherited'
		#   [set_pol] user request to (virtually) assign a particular policy
		faked_policy_reference = None
		if not is_container and not policy_dn:
			# case: [edit; w/pol; inherit]
			# -> current policy is (virtually) overwritten with 'None'
			faked_policy_reference = [None]
		elif is_container and policy_dn:
			# cases:
			# * [new; w/pol; inherit]
			# * [new; w/pol; set_pol]
			# -> old + temporary policy are both (virtually) set at the parent container
			faked_policy_reference = obj.policies + [policy_dn]
		else:
			# cases:
			# * [new; w/o_pol; inherit]
			# * [new; w/o_pol; set_pol]
			# * [edit; w/pol; set_pol]
			# * [edit; w/o_pol; inherit]
			# * [edit; w/o_pol; set_pol]
			faked_policy_reference = [policy_dn]

		policy_obj.policy_result(faked_policy_reference)
		infos = copy.copy(policy_obj.polinfo_more)
		for key, value in infos.items():
			if key in policy_obj.polinfo:
				if isinstance(infos[key], (tuple, list)):
					continue
				infos[key]['value'] = policy_obj.polinfo[key]
		return infos


class Operations(Ressource):
	"""GET /udm/progress/$progress-id (get the progress of a started operation like move, report, maybe add/put?, ...)"""

	def get(self, progress):
		return


def start():
	if os.fork() > 0:
		os._exit(0)
	run()


def run():
	module_type = '([a-z]+)'
	object_type = '([a-z]+/[a-z_]+)'
	policies_object_type = '(policies/[a-z_]+)'
	dn = '([^/]+(?:=|%3d|%3D)[^/]+)'  # Bug in tornado: requests go against the raw url; https://github.com/tornadoweb/tornado/issues/2548
	property_ = '([^/]+)'
	application = Application([
		(r"/favicon.ico", Favicon),
		(r"/udm/", Modules),
		(r"/udm/relation/.*", Relations),
		(r"/udm/license/", License),
		(r"/udm/license/check", LicenseCheck),
		(r"/udm/license/request", LicenseRequest),
		(r"/udm/navigation/", ObjectTypesNavigation),
		(r"/udm/%s/containers/" % (object_type,), Navigation),
		(r"/udm/%s/properties" % (object_type,), Properties),
		(r"/udm/%s/" % (module_type,), ObjectTypes),
		(r"/udm/(navigation)/containers/", Navigation),
		(r"/udm/(%s|navigation)/move-destinations/" % (object_type,), MoveDestinations),
		(r"/udm/%s/options" % (object_type,), Options),
		(r"/udm/%s/templates" % (object_type,), Templates),
		(r"/udm/%s/containers" % (object_type,), Containers),  # TODO: maybe rename conflicts with above except trailing slash
		(r"/udm/%s/policies" % (object_type,), Policies),
		(r"/udm/%s/report-types" % (object_type,), ReportTypes),
		(r"/udm/%s/report/([^/]+)" % (object_type,), Report),
		(r"/udm/%s/%s/properties/" % (object_type, dn), Properties),
		(r"/udm/%s/%s/properties/%s/choices" % (object_type, dn, property_), PropertyChoices),
		(r"/udm/%s/properties/%s/default" % (object_type, property_), DefaultValue),
		(r"/udm/%s/%s/%s/" % (object_type, dn, policies_object_type), PolicyTypes),
		(r"/udm/%s/%s/%s/" % (object_type, policies_object_type, dn), PolicyResult),
		(r"/udm/%s/add" % (object_type,), ObjectAdd),
		(r"/udm/%s/" % (object_type,), Objects),
		(r"/udm/%s/%s" % (object_type, dn), Object),
		(r"/udm/%s/%s/edit" % (object_type, dn), ObjectEdit),
		(r"/udm/%s/layout" % (object_type,), Layout),
		(r"/udm/%s/%s/layout" % (object_type, dn), Layout),
		(r"/udm/networks/network/([^/]+)/next-free-ip-address", NextFreeIpAddress),
		(r"/udm/progress/([0-9]+)", Operations),
		# TODO: meta info
		# TODO: decorator for dn argument, which makes sure no invalid dn syntax is used
	])
	application.listen(8888)
	tornado.ioloop.IOLoop.current().start()


if __name__ == "__main__":
	parser = argparse.ArgumentParser()
	subparsers = parser.add_subparsers(title='actions', description='All available actions')
	start_parser = subparsers.add_parser('start', description='Start the service')
	start_parser.set_defaults(func=start)
	run_parser = subparsers.add_parser('run', description='Start the service in foreground')
	run_parser.set_defaults(func=run)
	args = parser.parse_args()
	args.func()
