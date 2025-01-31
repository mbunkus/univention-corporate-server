# -*- coding: utf-8 -*-
#
# Copyright 2013-2021 Univention GmbH
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

"""
ALPHA VERSION

Wrapper around Univention Directory Manager CLI to simplify
creation/modification of UDM objects in python. The wrapper automatically
removed created objects during wrapper destruction.
For usage examples look at the end of this file.

WARNING:
The API currently allows only modifications to objects created by the wrapper
itself. Also the deletion of objects is currently unsupported. Also not all
UDM object types are currently supported.

WARNING2:
The API is currently under heavy development and may/will change before next UCS release!
"""

from __future__ import print_function

import copy
import functools
import os
import pipes
import random
import subprocess
import sys
import time
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Text, Tuple, Union  # noqa F401

import ldap
import ldap.filter
import psutil
import six

import univention.admin.modules
import univention.admin.objects
import univention.admin.uldap
import univention.testing.strings as uts
import univention.testing.ucr
import univention.testing.utils as utils
from univention.testing.ucs_samba import wait_for_drs_replication, DRSReplicationFailed

try:
	from inspect import getfullargspec as getargspec
except ImportError:
	from inspect import getargspec  # python 2


class UCSTestUDM_Exception(Exception):

	def __str__(self):
		if self.args and len(self.args) == 1 and isinstance(self.args[0], dict):
			return '\n'.join('%s=%s' % (key, value) for key, value in self.args[0].items())
		else:
			return Exception.__str__(self)
	__repr__ = __str__


class UCSTestUDM_MissingModulename(UCSTestUDM_Exception):
	pass


class UCSTestUDM_MissingDn(UCSTestUDM_Exception):
	pass


class UCSTestUDM_CreateUDMObjectFailed(UCSTestUDM_Exception):
	pass


class UCSTestUDM_CreateUDMUnknownDN(UCSTestUDM_Exception):
	pass


class UCSTestUDM_ModifyUDMObjectFailed(UCSTestUDM_Exception):
	pass


class UCSTestUDM_MoveUDMObjectFailed(UCSTestUDM_Exception):
	pass


class UCSTestUDM_NoModification(UCSTestUDM_Exception):
	pass


class UCSTestUDM_ModifyUDMUnknownDN(UCSTestUDM_Exception):
	pass


class UCSTestUDM_RemoveUDMObjectFailed(UCSTestUDM_Exception):
	pass


class UCSTestUDM_CleanupFailed(UCSTestUDM_Exception):
	pass


class UCSTestUDM_CannotModifyExistingObject(UCSTestUDM_Exception):
	pass


class UCSTestUDM_ListUDMObjectFailed(UCSTestUDM_Exception):
	pass


class UCSTestUDM(object):
	PATH_UDM_CLI_SERVER = '/usr/share/univention-directory-manager-tools/univention-cli-server'
	PATH_UDM_CLI_CLIENT = '/usr/sbin/udm'
	PATH_UDM_CLI_CLIENT_WRAPPED = '/usr/sbin/udm-test'

	COMPUTER_MODULES = (
		'computers/ubuntu',
		'computers/linux',
		'computers/windows',
		'computers/windows_domaincontroller',
		'computers/domaincontroller_master',
		'computers/domaincontroller_backup',
		'computers/domaincontroller_slave',
		'computers/memberserver',
		'computers/macos',
		'computers/ipmanagedclient')

	# map identifying UDM module or rdn-attribute to samba4 rdn attribute
	def ad_object_identifying_filter(self, modulename, dn):
		# type: (str, str) -> Optional[Dict[str, str]]
		udm_mainmodule, udm_submodule = modulename.split('/', 1)
		objname = ldap.dn.str2dn(dn)[0][0][1]

		attr = ''
		ad_ldap_controls = None
		con_search_filter = ''
		match_filter = ''

		if udm_mainmodule == 'users':
			attr = 'sAMAccountName'
			con_search_filter = '(&(objectClass=user)(!(objectClass=computer))(userAccountControl:1.2.840.113556.1.4.803:=512))'
			match_filter = '(&(|(&(objectClass=posixAccount)(objectClass=krb5Principal))(objectClass=user))(!(objectClass=univentionHost)))'
		elif udm_mainmodule == 'groups':
			attr = 'sAMAccountName'
			con_search_filter = '(objectClass=group)'
		elif udm_mainmodule == 'computers':
			if udm_submodule.startswith('domaincontroller_') or udm_submodule == 'windows_domaincontroller':
				attr = 'cn'
				con_search_filter = '(&(objectClass=computer)(userAccountControl:1.2.840.113556.1.4.803:=532480))'
				match_filter = '(|(&(objectClass=univentionDomainController)(univentionService=Samba 4))(objectClass=computer)(univentionServerRole=windows_domaincontroller))'
			elif udm_submodule in ('windows', 'memberserver', 'linux', 'ubuntu', 'macos'):
				attr = 'cn'
				con_search_filter = '(&(objectClass=computer)(userAccountControl:1.2.840.113556.1.4.803:=4096))'
				match_filter = '(|(&(objectClass=univentionWindows)(!(univentionServerRole=windows_domaincontroller)))(objectClass=computer)(objectClass=univentionMemberServer)(objectClass=univentionUbuntuClient)(objectClass=univentionLinuxClient)(objectClass=univentionMacOSClient))'
		elif modulename == 'containers/cn':
			attr = 'cn'
			con_search_filter = '(&(|(objectClass=container)(objectClass=builtinDomain))(!(objectClass=groupPolicyContainer)))'
		elif modulename == 'container/msgpo':
			attr = 'cn'
			con_search_filter = '(&(objectClass=container)(objectClass=groupPolicyContainer))'
		elif modulename == 'containers/ou':
			attr = 'ou'
			con_search_filter = 'objectClass=organizationalUnit'
		elif udm_mainmodule == 'dns':
			attr = 'dc'
			ad_ldap_controls = ["search_options:1:2"]
			if udm_submodule in ('alias', 'host_record', 'ptr_record', 'srv_record', 'txt_record', 'ns_record', 'host_record'):
				con_search_filter = '(&(objectClass=dnsNode)(!(dNSTombstoned=TRUE)))'
			elif udm_submodule in ('forward_zone', 'reverse_zone'):
				con_search_filter = '(objectClass=dnsZone)'  # partly true, actually we map the SOA too

		if match_filter:
			try:
				res = self._lo.search(base=dn, filter=match_filter, scope='base', attr=[])
			except ldap.NO_SUCH_OBJECT:
				print("OpenLDAP object to check against S4-Connector match_filter doesn't exist: %s" % (dn, ))
				res = None  # TODO: This happens during delete. By setting res=None here, we will not wait for DRS replication for deletes!
			except Exception as ex:
				print("OpenLDAP search with S4-Connector match_filter failed: %s" % (ex, ))
				raise
			if not res:
				print("DRS wait not required, S4-Connector match_filter did not match the OpenLDAP object: %s" % (dn,))
				return

		if attr:
			filter_template = '(&(%s=%%s)%s)' % (attr, con_search_filter)
			ad_ldap_search_args = {'ldap_filter': ldap.filter.filter_format(filter_template, (objname,)), 'controls': ad_ldap_controls}
			return ad_ldap_search_args

	__lo = None
	__ucr = None

	@property
	def _lo(self):
		# type: () -> univention.admin.uldap.access
		if self.__lo is None:
			self.__lo = utils.get_ldap_connection()
		return self.__lo

	@property
	def _ucr(self):
		# type: () -> univention.testing.ucr.UCSTestConfigRegistry
		if self.__ucr is None:
			self.__ucr = univention.testing.ucr.UCSTestConfigRegistry()
			self.__ucr.load()
		return self.__ucr

	@property
	def LDAP_BASE(self):
		# type: () -> str
		return self._ucr['ldap/base']

	@property
	def FQHN(self):
		# type: () -> str
		return '%(hostname)s.%(domainname)s.' % self._ucr

	@property
	def UNIVENTION_CONTAINER(self):
		# type: () -> str
		return 'cn=univention,%(ldap/base)s' % self._ucr

	@property
	def UNIVENTION_TEMPORARY_CONTAINER(self):
		# type: () -> str
		return 'cn=temporary,cn=univention,%(ldap/base)s' % self._ucr

	def __init__(self):
		# type: () -> None
		self._cleanup = {}
		self._cleanupLocks = {}

	@classmethod
	def _build_udm_cmdline(cls, modulename, action, kwargs):
		# type: (str, str, Dict[str, Any]) -> List[str]
		"""
		Pass modulename, action (create, modify, delete) and a bunch of keyword arguments
		to _build_udm_cmdline to build a command for UDM CLI.

		:param str modulename: name of UDM module (e.g. 'users/user')
		:param str action: An action, like 'create', 'modify', 'delete'.
		:param dict kwargs: A dictionary containing properties or one of the following special keys:

		:param str binddn: The LDAP simple-bind DN.
		:param str bindpwd: The LDAP simple-bind password.
		:param str bindpwdfile: A pathname to a file containing the LDAP simple-bind password.
		:param str dn: The LDAP distinguished name to operate on.
		:param str position: The LDAP distinguished name of the parent container.
		:param str superordinate: The LDAP distinguished name of the logical parent.
		:param str policy_reference: The LDAP distinguished name of the UDM policy to add.
		:param str policy_dereference: The LDAP distinguished name of the UDM policy to remove.
		:param str append_option: The name of an UDM option group to add.
		:param list options: A list of UDM option group to set.
		:param str_or_list set: A list or one single *name=value* property.
		:param list append: A list of *name=value* properties to add.
		:param list remove: A list of *name=value* properties to remove.
		:param boolean remove_referring: Remove other LDAP entries referred by this entry.
		:param boolean ignore_exists: Ignore error on creation if entry already exists.
		:param boolean ignore_not_exists: Ignore error on deletion if entry does not exists.

		>>> UCSTestUDM._build_udm_cmdline('users/user', 'create', {'username': 'foobar'})
		['/usr/sbin/udm-test', 'users/user', 'create', '--set', 'username=foobar']
		"""
		cmd = [cls.PATH_UDM_CLI_CLIENT_WRAPPED, modulename, action]
		args = copy.deepcopy(kwargs)

		for arg in ('binddn', 'bindpwd', 'bindpwdfile', 'dn', 'position', 'superordinate', 'policy_reference', 'policy_dereference', 'append_option'):
			if arg not in args:
				continue
			value = args.pop(arg)
			if not isinstance(value, (list, tuple)):
				value = (value,)
			for item in value:
				cmd.extend(['--%s' % arg.replace('_', '-'), item])

		if action == 'list' and 'policies' in args:
			cmd.extend(['--policies=%s' % (args.pop('policies'),)])

		if action == 'list' and 'filter' in args:
			cmd.extend(['--filter=%s' % (args.pop('filter'),)])

		for option in args.pop('options', ()):
			cmd.extend(['--option', option])

		for key, value in args.pop('set', {}).items():
			if isinstance(value, (list, tuple)):
				for item in value:
					cmd.extend(['--set', '%s=%s' % (key, item)])
			else:
				cmd.extend(['--set', '%s=%s' % (key, value)])

		for operation in ('append', 'remove'):
			for key, values in args.pop(operation, {}).items():
				for value in values:
					cmd.extend(['--%s' % operation, '%s=%s' % (key, value)])

		if args.pop('remove_referring', True) and action == 'remove':
			cmd.append('--remove_referring')

		if args.pop('ignore_exists', False) and action == 'create':
			cmd.append('--ignore_exists')

		if args.pop('ignore_not_exists', False) and action == 'remove':
			cmd.append('--ignore_not_exists')

		# set all other remaining properties
		for key, value in args.items():
			if isinstance(value, (list, tuple)):
				for item in value:
					cmd.extend(['--append', '%s=%s' % (key, item)])
			elif value:
				cmd.extend(['--set', '%s=%s' % (key, value)])

		return cmd

	def create_object(self, modulename, wait_for_replication=True, check_for_drs_replication=False, wait_for=False, **kwargs):
		# type: (str, bool, bool, bool, **Any) -> str
		r"""
		Creates a LDAP object via UDM. Values for UDM properties can be passed via keyword arguments
		only and have to exactly match UDM property names (case-sensitive!).

		:param str modulename: name of UDM module (e.g. 'users/user')
		:param bool wait_for_replication: delay return until Listener has settled.
		:param bool check_for_drs_replication: delay return until Samab4 has settled.
		:param \*\*kwargs:
		"""
		if not modulename:
			raise UCSTestUDM_MissingModulename()

		dn = None
		cmd = self._build_udm_cmdline(modulename, 'create', kwargs)
		print('Creating %s object with %s' % (modulename, _prettify_cmd(cmd)))
		child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=False)
		(stdout, stderr) = child.communicate()

		if six.PY3:
			stdout, stderr = stdout.decode('utf-8', 'replace'), stderr.decode('utf-8', 'replace')

		if child.returncode:
			raise UCSTestUDM_CreateUDMObjectFailed({'module': modulename, 'kwargs': kwargs, 'returncode': child.returncode, 'stdout': stdout, 'stderr': stderr})

		# find DN of freshly created object and add it to cleanup list
		for line in stdout.splitlines():  # :pylint: disable-msg=E1103
			if line.startswith('Object created: ') or line.startswith('Object exists: '):
				dn = line.split(': ', 1)[-1]
				if not line.startswith('Object exists: '):
					self._cleanup.setdefault(modulename, []).append(dn)
				break
		else:
			raise UCSTestUDM_CreateUDMUnknownDN({'module': modulename, 'kwargs': kwargs, 'stdout': stdout, 'stderr': stderr})

		self.wait_for(modulename, dn, wait_for_replication, everything=wait_for)
		return dn

	def create_with_defaults(self, modulename, **kwargs):
		# type: (str, **Any) -> Tuple[str, dict]
		"""Create any object with as maximum as possible prefilled random default values"""
		module = univention.admin.modules.get_module(modulename)

		if 'position' not in kwargs and not modulename.startswith('settings/portal'):
			kwargs['position'] = (module.object.get_default_containers(self._lo) or [self.LDAP_BASE])[0]

		superordinate_props = {}
		if 'superordinate' not in kwargs and getattr(module, 'superordinate', None) not in (None, 'settings/cn'):
			superordinate_module = random.choice(module.superordinate) if isinstance(module.superordinate, list) else module.superordinate
			superordinate, superordinate_props = self.create_with_defaults(superordinate_module, position=kwargs['position'])
			kwargs['superordinate'] = kwargs['position'] = superordinate

		max_recursion = kwargs.pop('max_recursion', 1)

		def ldap_search(prop):
			m, p = prop.syntax.value.split(': ', 1)
			if max_recursion <= 0:
				return  # random.choice(self._cleanup.get(m, [None]))
			return self.create_with_defaults(m, max_recursion=max_recursion - 1)[1][p]

		def udm_attribute(prop):
			if max_recursion <= 0:
				return  # random.choice(self._cleanup.get(prop.syntax.udm_module, [None]))
			return self.create_with_defaults(prop.syntax.udm_module, max_recursion=max_recursion - 1)[1][prop.syntax.attribute]

		def udm_objects(prop):
			m = list(reversed(prop.syntax.udm_modules))
			try:
				m.remove('computers/computer')
				m.append('computers/linux')
				m.append('computers/windows')
				m.append('computers/ubuntu')
			except ValueError:
				pass
			try:
				m.remove('computers/domaincontroller_master')
			except ValueError:
				pass

			if max_recursion <= 0:
				if prop.syntax.key == 'dn':
					return  # random.choice(self._cleanup.get(m[0], [None]))  # warning: would cause circular group memberships for groups/group
				return
			_dn, _props = self.create_with_defaults(m[0], max_recursion=max_recursion - 1)
			p = prop.syntax.key % _props
			if p == 'dn':
				return _dn
			return p

		syntax_classes_mapping = {
			'string': uts.random_string,
			'string_numbers_letters_dots': uts.random_string,
			'string_numbers_letters_dots_spaces': uts.random_string,
			'string64': lambda: uts.random_string(64),
			'string6': lambda: uts.random_string(6),
			'HalfString': uts.random_string,
			'OneThirdString': uts.random_string,
			'TwoThirdsString': uts.random_string,
			'FiveThirdsString': uts.random_string,
			'IA5string': uts.random_string,
			'integer': lambda: uts.random_int(0, 100000),
			'uid': uts.random_username,
			'gid': uts.random_groupname,
			'userPasswd': uts.random_string,
			'passwd': uts.random_string,
			'Country': lambda: random.choice(univention.admin.syntax.Country.choices)[0],
			'univentionAdminModules': lambda: random.choice(univention.admin.syntax.univentionAdminModules.choices)[0],
			'SambaPrivileges': lambda: random.choice(univention.admin.syntax.SambaPrivileges.choices)[0],
			'sambaGroupType': lambda: random.choice(univention.admin.syntax.sambaGroupType.choices)[0],
			'adGroupType': lambda: random.choice(univention.admin.syntax.adGroupType.choices)[0],
			'ipProtocol': lambda: random.choice(univention.admin.syntax.ipProtocol.choices)[0],
			'MAC_Address': uts.random_mac,
			'ipAddress': uts.random_ip,
			'absolutePath': lambda: '/' + uts.random_string(),
			'sharePath': lambda: '/' + uts.random_string(),
			'BaseFilename': lambda: '%s.%s' % (uts.random_string(), uts.random_string(3)),
			'PrinterURI': lambda: '%s %s' % (random.choice(['lpd://', 'ipp://', 'http://', 'usb:/', 'socket://', 'parallel:/', 'file:/', 'smb://']), uts.random_string()),
			'Base64Bzip2Text': lambda: __import__('base64').b64encode(__import__('bz2').compress(uts.random_string().encode())).decode('ASCII'),
			'emailAddress': lambda: '%s@%s.%s' % (uts.random_name(), uts.random_name(), uts.random_name()),
			'MailHomeServer': uts.random_domain_name,
			'boolean': lambda: uts.random_int(0, 1),
			'disabled': lambda: uts.random_int(0, 1),
			'locked': lambda: uts.random_int(0, 1),
			'v4netmask': lambda: uts.random_int(1, 31),
			'netmask': lambda: uts.random_int(1, 31),
			'IPv4_AddressRange': lambda: '%s.2 %s.254' % tuple([uts.random_ip().rsplit('.', 1)[0]] * 2),
			'printerName': lambda: uts.random_string(16),
			'DHCP_HardwareAddress': lambda: 'ethernet %s' % (uts.random_mac(),),
			'ipv4Address': uts.random_ip,
			'hostName': uts.random_string,
			'UNIX_TimeInterval': lambda: '%s %s' % (uts.random_int(), random.choice(univention.admin.syntax.Country.choices)[0]),
			'policyName': uts.random_string,
			'LocalizedDescription': lambda: '%s %s' % (random.choice(['de_DE', 'en_US']), uts.random_string()),
			'LocalizedDisplayName': lambda: '%s %s' % (random.choice(['de_DE', 'en_US']), uts.random_string()),
			'LocalizedLink': lambda: '%s %s://%s/%s' % (random.choice(['de_DE', 'en_US']), random.choice(['http', 'https']), uts.random_domain_name(), uts.random_string()),
			'reverseLookupSubnet': lambda: uts.random_ip().rsplit('.', 1)[0],
			'dnsPTR': lambda: uts.random_ip().rsplit('.', 1)[1],
			'dnsHostname': uts.random_domain_name,
			'dnsName': uts.random_domain_name,
			'dnsName_umlauts': uts.random_string,
			'dnsSRVName': lambda: 'ldap tcp %s' % (uts.random_string(),),
			'dnsSRVLocation': lambda: '%s %s %s %s' % (uts.random_int(), uts.random_int(), uts.random_int(), uts.random_domain_name()),
			'mailinglist_name': uts.random_string,
			'mail_folder_name': uts.random_string,
			'date': lambda: '20%02d-%02d-%02d' % (random.randint(0, 99), random.randint(1, 12), random.randint(1, 27)),
			'date2': lambda: '20%02d-%02d-%02d' % (random.randint(0, 99), random.randint(1, 12), random.randint(1, 27)),
			'iso8601Date': lambda: '20%02d-%02d-%02d' % (random.randint(0, 99), random.randint(1, 12), random.randint(1, 27)),
			'phone': lambda: '+49 421 %s-%s' % (uts.random_int(10000, 99000), uts.random_int(0, 9)),
			'postalAddress': lambda: '"%s street 1A" "%s" "%s"' % (uts.random_string(), uts.random_int(10000, 99999), uts.random_string()),
			'keyAndValue': lambda: '%s %s' % (uts.random_string(), uts.random_string()),
			'SambaLogonHours': lambda: uts.random_int(0, 167),
			'DebianPackageVersion': uts.random_version,
			# 'UCSVersion': uts.random_version,
			'LDAP_Search': ldap_search,
			'GroupDN': udm_objects,
			'UserDN': udm_objects,
			'HostDN': udm_objects,
			'UCS_Server': udm_objects,
			'Windows_Server': udm_objects,
			'DomainController': udm_objects,
			'ServicePrint_FQDN': udm_objects,
			'printerModel': lambda: '"%s" "%s"' % (random.choice(['smb', 'cupsfilters/pxlmono.ppd', 'hp-ppd/HP/HP_LaserJet_6P.ppd', 'cups-pdf/CUPS-PDF_opt.ppd']), uts.random_string()),
			'PrinterDriverList': udm_attribute,
			'PrinterNames': udm_objects,
			# 'network': uts.random_string,
			# 'UvmmCloudType': uts.random_string,
			# 'emailForwardSetting': uts.random_string,
			# 'jpegPhoto': uts.random_string,
			# 'WritableShare': uts.random_string,
			# 'Base64Upload': uts.random_string,
			# 'ActivationDateTimeTimezone': uts.random_string,
			# 'emailAddressValidDomain': uts.random_string,
			# 'primaryEmailAddressValidDomain'
			# 'dhcpEntry': uts.random_string,
			# 'Service': uts.random_string,
			# 'dnsEntryReverse': uts.random_string,
			# 'nagiosHostsEnabledDn': uts.random_string,
			# 'nagiosServiceDn': uts.random_string,
			# 'dnsEntryAlias': uts.random_string,
			# 'dnsEntry': uts.random_string,
		}
		module_property_mapping = {
			'sambaRID': lambda: uts.random_int(1000, 9999),
			'mailForwardAddress': None,  # depends on mailPrimaryAddress
			'preferredDeliveryMethod': lambda: random.choice(["any", "mhs", "physical", "telex", "teletex", "g3fax", "g4fax", "ia5", "videotex", "telephone"]),
			'shares/share': {
				'sambaCustomSettings': lambda: random.choice(['"acl xattr update mtime" yes', '"access based share enum" yes', '"follow symlinks" "yes"']),
			},
			'dns/reverse_zone': {
				'contact': syntax_classes_mapping['emailAddress'],  # Bug #53794
			},
			'dns/ptr_record': {
				'ip': None,  # prevent, that a ip is set. instead address is set, which builds the ip from address.$superordinate
			},
			'settings/mswmifilter': {
				'description': None,  # Bug #53797
				'displayName': None,  # Bug #53797
			},
		}
		for name, prop in module.property_descriptions.items():
			if name in kwargs:
				continue
			if not prop.editable:  # or (is_modification and not prop.may_change)
				continue
			func = module_property_mapping.get(modulename, {}).get(name, module_property_mapping.get(name, syntax_classes_mapping.get(prop.syntax.name)))
			if not func:
				continue

			if 'prop' in getargspec(func).args:
				func = functools.partial(func, prop)

			value = list(set(func() for i in range(random.randint(int(prop.required or name in ('ip', 'range')), 4)))) if prop.multivalue else func()
			if value is None or isinstance(value, list) and all(v is None for v in value):
				continue
			kwargs.setdefault(name, value)

		if modulename == 'shares/printer':
			# when creating a shares/printergroup recursion is prevented: circular references aren't created
			# therefore set some (invalid) values here
			kwargs.setdefault('spoolHost', 'localhost')
			kwargs.setdefault('model', 'cups-pdf/CUPS-PDF_noopt.ppd FAKE')

		if modulename in ('dhcp/subnet', 'dhcp/sharedsubnet'):
			import ipaddress
			kwargs['subnetmask'] = str(min(29, int(kwargs['subnetmask'])))
			iface = ipaddress.IPv4Interface(u'%(subnet)s/%(subnetmask)s' % kwargs)
			kwargs['subnet'] = str(iface.network.network_address)
		elif modulename in ('dhcp/pool',):
			import ipaddress
			iface = ipaddress.IPv4Interface(u'%(subnet)s/%(subnetmask)s' % superordinate_props)
			if kwargs.get('dynamic_bootp_clients') != 'deny':
				kwargs.pop('failover_peer')
		if modulename in ('dhcp/subnet', 'dhcp/sharedsubnet', 'dhcp/pool'):
			hosts = iface.network.hosts()
			next(hosts)
			ranges = []
			for i in range(len(kwargs['range']) if isinstance(kwargs['range'], list) else 1):
				first = last = None
				try:
					first = last = next(hosts)
					for i in range(random.randrange(20)):
						last = next(hosts)
				except StopIteration:
					pass
				if first and first != last:
					ranges.append('%s %s' % (first, last))
				else:
					break
			kwargs['range'] = ranges

		return self.create_object(modulename, **kwargs), kwargs

	def modify_object(self, modulename, wait_for_replication=True, check_for_drs_replication=False, wait_for=False, **kwargs):
		# type: (str, bool, bool, bool, **Any) -> str
		"""
		Modifies a LDAP object via UDM. Values for UDM properties can be passed via keyword arguments
		only and have to exactly match UDM property names (case-sensitive!).
		Please note: the object has to be created by create_object otherwise this call will raise an exception!

		:param str modulename: name of UDM module (e.g. 'users/user')
		"""
		if not modulename:
			raise UCSTestUDM_MissingModulename()
		dn = kwargs.get('dn')
		if not dn:
			raise UCSTestUDM_MissingDn()
		if dn not in self._cleanup.get(modulename, set()):
			raise UCSTestUDM_CannotModifyExistingObject(dn)

		cmd = self._build_udm_cmdline(modulename, 'modify', kwargs)
		print('Modifying %s object with %s' % (modulename, _prettify_cmd(cmd)))
		child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=False)
		(stdout, stderr) = child.communicate()

		if six.PY3:
			stdout, stderr = stdout.decode('utf-8', 'replace'), stderr.decode('utf-8', 'replace')

		if child.returncode:
			raise UCSTestUDM_ModifyUDMObjectFailed({'module': modulename, 'kwargs': kwargs, 'returncode': child.returncode, 'stdout': stdout, 'stderr': stderr})

		for line in stdout.splitlines():  # :pylint: disable-msg=E1103
			if line.startswith('Object modified: '):
				dn = line.split('Object modified: ', 1)[-1]
				if dn != kwargs.get('dn'):
					print('modrdn detected: %r ==> %r' % (kwargs.get('dn'), dn))
					if kwargs.get('dn') in self._cleanup.get(modulename, []):
						self._cleanup.setdefault(modulename, []).append(dn)
						self._cleanup[modulename].remove(kwargs.get('dn'))
				break
			elif line.startswith('No modification: '):
				raise UCSTestUDM_NoModification({'module': modulename, 'kwargs': kwargs, 'stdout': stdout, 'stderr': stderr})
		else:
			raise UCSTestUDM_ModifyUDMUnknownDN({'module': modulename, 'kwargs': kwargs, 'stdout': stdout, 'stderr': stderr})

		self.wait_for(modulename, dn, wait_for_replication, everything=wait_for)
		return dn

	def move_object(self, modulename, wait_for_replication=True, check_for_drs_replication=False, wait_for=False, **kwargs):
		# type: (str, bool, bool, bool, **Any) -> str
		if not modulename:
			raise UCSTestUDM_MissingModulename()
		dn = kwargs.get('dn')
		if not dn:
			raise UCSTestUDM_MissingDn()
		if dn not in self._cleanup.get(modulename, set()):
			raise UCSTestUDM_CannotModifyExistingObject(dn)

		cmd = self._build_udm_cmdline(modulename, 'move', kwargs)
		print('Moving %s object %s' % (modulename, _prettify_cmd(cmd)))
		child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=False)
		(stdout, stderr) = child.communicate()

		if six.PY3:
			stdout, stderr = stdout.decode('utf-8', 'replace'), stderr.decode('utf-8', 'replace')

		if child.returncode:
			raise UCSTestUDM_MoveUDMObjectFailed({'module': modulename, 'kwargs': kwargs, 'returncode': child.returncode, 'stdout': stdout, 'stderr': stderr})

		for line in stdout.splitlines():  # :pylint: disable-msg=E1103
			if line.startswith('Object modified: '):
				self._cleanup.get(modulename, []).remove(dn)

				new_dn = ldap.dn.dn2str(ldap.dn.str2dn(dn)[0:1] + ldap.dn.str2dn(kwargs.get('position', '')))
				self._cleanup.setdefault(modulename, []).append(new_dn)
				break
		else:
			raise UCSTestUDM_ModifyUDMUnknownDN({'module': modulename, 'kwargs': kwargs, 'stdout': stdout, 'stderr': stderr})

		self.wait_for(modulename, dn, wait_for_replication, everything=wait_for)
		return new_dn

	def remove_object(self, modulename, wait_for_replication=True, wait_for=False, **kwargs):
		# type: (str, bool, bool, **Any) -> None
		if not modulename:
			raise UCSTestUDM_MissingModulename()
		dn = kwargs.get('dn')
		if not dn:
			raise UCSTestUDM_MissingDn()
		if dn not in self._cleanup.get(modulename, set()):
			raise UCSTestUDM_CannotModifyExistingObject(dn)

		cmd = self._build_udm_cmdline(modulename, 'remove', kwargs)
		print('Removing %s object %s' % (modulename, _prettify_cmd(cmd)))
		child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=False)
		(stdout, stderr) = child.communicate()

		if six.PY3:
			stdout, stderr = stdout.decode('utf-8', 'replace'), stderr.decode('utf-8', 'replace')

		if child.returncode:
			raise UCSTestUDM_RemoveUDMObjectFailed({'module': modulename, 'kwargs': kwargs, 'returncode': child.returncode, 'stdout': stdout, 'stderr': stderr})

		if dn in self._cleanup.get(modulename, []):
			self._cleanup[modulename].remove(dn)

		self.wait_for(modulename, dn, wait_for_replication, everything=wait_for)

	def wait_for(self, modulename, dn, wait_for_replication=True, wait_for_drs_replication=False, wait_for_s4connector=False, everything=False):
		# type: (str, str, bool, bool, bool, bool) -> None
		# the order of the conditions is imporant
		conditions = []
		if wait_for_replication:
			conditions.append((utils.ReplicationType.LISTENER, wait_for_replication))

		if everything:
			wait_for_drs_replication = True
			wait_for_s4connector = True
		drs_replication = wait_for_drs_replication
		ad_ldap_search_args = self.ad_object_identifying_filter(modulename, dn)
		if wait_for_drs_replication and not isinstance(wait_for_drs_replication, six.string_types):
			drs_replication = False
			if ad_ldap_search_args:
				drs_replication = ad_ldap_search_args

		if wait_for_s4connector and ad_ldap_search_args:
			if self._ucr.get('samba4/ldap/base'):
				conditions.append((utils.ReplicationType.S4C_FROM_UCS, ad_ldap_search_args))

		if drs_replication:
			if not wait_for_replication:
				conditions.append((utils.ReplicationType.LISTENER, wait_for_replication))

			if self._ucr.get('server/role') in ('domaincontroller_backup', 'domaincontroller_slave', 'memberserver'):
				conditions.append((utils.ReplicationType.DRS, drs_replication))

		return utils.wait_for(conditions, verbose=False)

	def create_user(self, wait_for_replication=True, check_for_drs_replication=True, wait_for=True, **kwargs):  # :pylint: disable-msg=W0613
		# type: (bool, bool, bool, **Any) -> Tuple[str, str]
		"""
		Creates a user via UDM CLI. Values for UDM properties can be passed via keyword arguments only and
		have to exactly match UDM property names (case-sensitive!). Some properties have default values:

		:param str position: 'cn=users,$ldap_base'
		:param str password: 'univention'
		:param str firstname: 'Foo Bar'
		:param str lastname: <random string>
		:param str username: <random string> If username is missing, a random user name will be used.
		:return: (dn, username)
		"""

		attr = self._set_module_default_attr(kwargs, (
			('position', 'cn=users,%s' % self.LDAP_BASE),
			('password', 'univention'),
			('username', uts.random_username()),
			('lastname', uts.random_name()),
			('firstname', uts.random_name())
		))

		return (self.create_object('users/user', wait_for_replication, check_for_drs_replication, wait_for=wait_for, **attr), attr['username'])

	def create_ldap_user(self, wait_for_replication=True, check_for_drs_replication=False, **kwargs):  # :pylint: disable-msg=W0613
		# type: (bool, bool, **Any) -> Tuple[str, str]
		# check_for_drs_replication=False -> ldap users are not replicated to s4
		attr = self._set_module_default_attr(kwargs, (
			('position', 'cn=users,%s' % self.LDAP_BASE),
			('password', 'univention'),
			('username', uts.random_username()),
			('lastname', uts.random_name()),
			('name', uts.random_name())
		))

		return (self.create_object('users/ldap', wait_for_replication, check_for_drs_replication, **attr), attr['username'])

	def remove_user(self, username, wait_for_replication=True):
		# type: (str, bool) -> None
		"""Removes a user object from the ldap given it's username."""
		kwargs = {
			'dn': 'uid=%s,cn=users,%s' % (username, self.LDAP_BASE)
		}
		self.remove_object('users/user', wait_for_replication, **kwargs)

	def create_group(self, wait_for_replication=True, check_for_drs_replication=True, **kwargs):  # :pylint: disable-msg=W0613
		# type: (bool, bool, **Any) -> Tuple[str, str]
		"""
		Creates a group via UDM CLI. Values for UDM properties can be passed via keyword arguments only and
		have to exactly match UDM property names (case-sensitive!). Some properties have default values:

		:param str position: `cn=users,$ldap_base`
		:param str name: <random value>
		:return: (dn, groupname)

		If "groupname" is missing, a random group name will be used.
		"""
		attr = self._set_module_default_attr(kwargs, (
			('position', 'cn=groups,%s' % self.LDAP_BASE),
			('name', uts.random_groupname())
		))

		return (self.create_object('groups/group', wait_for_replication, check_for_drs_replication, **attr), attr['name'])

	def _set_module_default_attr(self, attributes, defaults):
		"""
		Returns the given attributes, extended by every property given in defaults if not yet set.

		:param tuple defaults: should be a tupel containing tupels like "('username', <default_value>)".
		"""
		attr = copy.deepcopy(attributes)
		for prop, value in defaults:
			attr.setdefault(prop, value)
		return attr

	def addCleanupLock(self, lockType, lockValue):
		self._cleanupLocks.setdefault(lockType, []).append(lockValue)

	def _wait_for_drs_removal(self, modulename, dn, verbose=True):
		# type: (str, str, bool) -> None
		ad_ldap_search_args = self.ad_object_identifying_filter(modulename, dn)
		if ad_ldap_search_args:
			wait_for_drs_replication(should_exist=False, verbose=verbose, timeout=20, **ad_ldap_search_args)

	def list_objects(self, modulename, **kwargs):
		# type: (str, **Any) -> List[Tuple[str, Dict[str, Any]]]
		cmd = self._build_udm_cmdline(modulename, 'list', kwargs)
		print('Listing %s objects %s' % (modulename, _prettify_cmd(cmd)))
		child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=False)
		(stdout, stderr) = child.communicate()

		if six.PY3:
			stdout, stderr = stdout.decode('utf-8', 'replace'), stderr.decode('utf-8', 'replace')

		if child.returncode:
			raise UCSTestUDM_ListUDMObjectFailed(child.returncode, stdout, stderr)

		objects = []  # type: List[Tuple[str, Dict[str, Any]]]
		dn = None
		attrs = {}  # type: Dict[str, Any]
		pattr = None
		pvalue = None
		pdn = None
		current_policy_type = None
		for line in stdout.splitlines():
			if line.startswith('DN: '):
				if dn:
					objects.append((dn, attrs))
					dn = None
					attrs = {}
				dn = line[3:].strip()
			elif not line.strip():
				continue
			elif line.startswith('    ') and ':' in line:  # list --policies=1
				name, value = line.split(':', 1)
				if name.strip() == 'Policy':
					pvalue = pattr = None
					pdn = value
				elif name.strip() == 'Attribute':
					pattr = value
				elif name.strip() == 'Value':
					pvalue = value
					attrs.setdefault(current_policy_type, {}).setdefault(pdn.strip(), {}).setdefault(pattr.strip(), []).append(pvalue.strip())
			elif line.startswith('    ') and '=' in line:  # list --policies=2
				name, value = line.split('=', 1)
				attrs.setdefault(current_policy_type, {}).setdefault(name.strip(), []).append(value.strip().strip('"'))
			elif any(x in line for x in ('Policy-based Settings', 'Subnet-based Settings', 'Merged Settings')):
				current_policy_type = line.split(':')[0].strip()
			elif line.startswith(' ') and ':' in line:
				name, value = line.split(':', 1)
				attrs.setdefault(name.strip(), []).append(value.strip())
		if dn:
			objects.append((dn, attrs))
		return objects

	def cleanup(self):
		# type: () -> None
		"""
		Automatically removes LDAP objects via UDM CLI that have been created before.
		"""
		failedObjects = {}
		print('Performing UCSTestUDM cleanup...')
		objects = []
		removed = []
		for modulename, objs in self._cleanup.items():
			objects.extend((modulename, dn) for dn in objs)

		for modulename, dn in sorted(objects, key=lambda x: len(x[1]), reverse=True):
			cmd = ['/usr/sbin/udm-test', modulename, 'remove', '--dn', dn, '--remove_referring']

			print('removing DN:', dn)
			child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=False)
			(stdout, stderr) = child.communicate()
			if six.PY3:
				stdout, stderr = stdout.decode('utf-8', 'replace'), stderr.decode('utf-8', 'replace')
			if child.returncode or 'Object removed:' not in stdout:
				failedObjects.setdefault(modulename, []).append(dn)
			else:
				removed.append((modulename, dn))

		# simply iterate over the remaining objects again, removing them might just have failed for chronology reasons
		# (e.g groups can not be removed while there are still objects using it as primary group)
		for modulename, objects in failedObjects.items():
			for dn in objects:
				cmd = ['/usr/sbin/udm-test', modulename, 'remove', '--dn', dn, '--remove_referring']

				child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=False)
				(stdout, stderr) = child.communicate()
				if six.PY3:
					stdout, stderr = stdout.decode('utf-8', 'replace'), stderr.decode('utf-8', 'replace')

				if child.returncode or 'Object removed:' not in stdout:
					print('Warning: Failed to remove %r object %r' % (modulename, dn), file=sys.stderr)
					print('stdout=%r %r %r' % (stdout, stderr, self._lo.get(dn)), file=sys.stderr)
				else:
					removed.append((modulename, dn))
		self._cleanup = {}

		for lock_type, values in self._cleanupLocks.items():
			for value in values:
				lockDN = 'cn=%s,cn=%s,%s' % (value, lock_type, self.UNIVENTION_TEMPORARY_CONTAINER)
				try:
					self._lo.delete(lockDN)
				except ldap.NO_SUCH_OBJECT:
					pass
				except Exception as ex:
					print('Failed to remove locking object "%s" during cleanup: %r' % (lockDN, ex))
		self._cleanupLocks = {}

		print('Cleanup: wait for replication and drs removal')
		utils.wait_for_replication(verbose=False)
		for module, dn in removed:
			try:
				self._wait_for_drs_removal(module, dn, verbose=True)
			except DRSReplicationFailed as exc:
				print('Cleanup: DRS replication failed:', exc)

		self.stop_cli_server()
		print('UCSTestUDM cleanup done')

	def stop_cli_server(self):
		# type: () -> None
		""" restart UDM CLI server """
		print('trying to restart UDM CLI server')
		procs = []
		for proc in psutil.process_iter():
			try:
				cmdline = proc.cmdline()
				if len(cmdline) >= 2 and cmdline[0].startswith('/usr/bin/python') and cmdline[1] == self.PATH_UDM_CLI_SERVER:
					procs.append(proc)
			except psutil.NoSuchProcess:
				pass
		for signal in (15, 9):
			for proc in procs:
				try:
					print('sending signal %s to process %s (%r)' % (signal, proc.pid, proc.cmdline(),))
					os.kill(proc.pid, signal)
				except (psutil.NoSuchProcess, EnvironmentError):
					print('process already terminated')
					procs.remove(proc)
			if signal == 15:
				time.sleep(1)

	def verify_udm_object(self, *args, **kwargs):
		return verify_udm_object(*args, **kwargs)

	def verify_ldap_object(self, *args, **kwargs):
		return utils.verify_ldap_object(*args, **kwargs)

	def __enter__(self):
		return self

	def __exit__(self, exc_type, exc_value, traceback):
		if exc_type:
			print('Cleanup after exception: %s %s' % (exc_type, exc_value))
		self.cleanup()


class UDM(UCSTestUDM):
	"""UDM interface using the REST API"""

	PATH_UDM_CLI_CLIENT_WRAPPED = '/usr/sbin/udm-test-rest'

	def stop_cli_server(self):
		# type: () -> None
		super(UDM, self).stop_cli_server()
		subprocess.call(['systemctl', 'reload', 'univention-directory-manager-rest.service'])


def verify_udm_object(module, dn, expected_properties):
	# type: (Any, str, Optional[Mapping[str, Union[bytes, Text, Tuple[str, ...], List[str]]]]) -> None
	"""
	Verify an object exists with the given `dn` in the given UDM `module` with
	some properties. Setting `expected_properties` to `None` requires the
	object to not exist.
	:param dict expected_properties: is a dictionary of (property,value) pairs.

	:raises AssertionError: in case of a mismatch.
	"""
	lo = utils.get_ldap_connection(admin_uldap=True)
	try:
		position = univention.admin.uldap.position(lo.base)
		udm_module = univention.admin.modules.get(module)
		if not udm_module:
			univention.admin.modules.update()
			udm_module = univention.admin.modules.get(module)
		udm_object = univention.admin.objects.get(udm_module, None, lo, position, dn)
		udm_object.open()
	except univention.admin.uexceptions.noObject:
		if expected_properties is None:
			return
		raise

	if expected_properties is None:
		raise AssertionError("UDM object {} should not exist".format(dn))

	difference = {}
	for (key, value) in expected_properties.items():
		udm_value = udm_object.info.get(key, [])
		if udm_value is None:
			udm_value = []
		if isinstance(udm_value, (bytes, six.string_types)):
			udm_value = {udm_value}
		if not isinstance(value, (tuple, list)):
			value = {value}
		value = {_to_unicode(v).lower() for v in value}
		udm_value = {_to_unicode(v).lower() for v in udm_value}
		if udm_value != value:
			try:
				value = {_normalize_dn(dn) for dn in value}
				udm_value = {_normalize_dn(dn) for dn in udm_value}
			except ldap.DECODING_ERROR:
				pass
		if udm_value != value:
			difference[key] = (udm_value, value)
	assert not difference, '\n'.join('{}: {} != expected {}'.format(key, udm_value, value) for key, (udm_value, value) in difference.items())


def _prettify_cmd(cmd):
	# type: (Iterable[str]) -> str
	cmd = ' '.join(pipes.quote(x) for x in cmd)
	if set(cmd) & {'\x00', '\n'}:
		cmd = repr(cmd)
	return cmd


def _to_unicode(string):
	# type: (Union[bytes, Text]) -> Text
	if isinstance(string, bytes):
		return string.decode('utf-8')
	return string


def _normalize_dn(dn):
	# type: (str) -> str
	r"""
	Normalize a given dn. This removes some escaping of special chars in the
	DNs. Note: The CON-LDAP returns DNs with escaping chars, OpenLDAP does not.

	>>> _normalize_dn(r"cn=peter\#,cn=groups")
	'cn=peter#,cn=groups'
	"""
	return ldap.dn.dn2str(ldap.dn.str2dn(dn))


if __name__ == '__main__':
	import doctest
	print(doctest.testmod())

if __name__ == '__disabled__':
	ucr = univention.testing.ucr.UCSTestConfigRegistry()
	ucr.load()

	with UCSTestUDM() as udm:
		# create user
		dnUser, _username = udm.create_user()

		# stop CLI daemon
		udm.stop_cli_server()

		# create group
		_dnGroup, _groupname = udm.create_group()

		# modify user from above
		udm.modify_object('users/user', dn=dnUser, description='Foo Bar')

		# test with malformed arguments
		try:
			_dnUser, _username = udm.create_user(username='')
		except UCSTestUDM_CreateUDMObjectFailed:
			print('Caught anticipated exception UCSTestUDM_CreateUDMObjectFailed - SUCCESS')

		# try to modify object not created by create_udm_object()
		try:
			udm.modify_object('users/user', dn='uid=Administrator,cn=users,%s' % ucr.get('ldap/base'), description='Foo Bar')
		except UCSTestUDM_CannotModifyExistingObject:
			print('Caught anticipated exception UCSTestUDM_CannotModifyExistingObject - SUCCESS')
