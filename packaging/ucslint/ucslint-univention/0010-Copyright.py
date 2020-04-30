# -*- coding: utf-8 -*-
#
# Copyright (C) 2008-2020 Univention GmbH
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

try:
	import univention.ucslint.base as uub
except ImportError:
	import ucslint.base as uub
import re
import os
import time


RE_SKIP = re.compile(
	'|'.join((
		'temporary wrapper script for',
		'Generated by ltmain.sh',
		'This file is maintained in Automake',
	)))
DEP5 = "Format: https://www.debian.org/doc/packaging-manuals/copyright-format/1.0/"


class UniventionPackageCheck(uub.UniventionPackageCheckDebian):

	def getMsgIds(self):
		return {
			'0010-1': [uub.RESULT_WARN, 'failed to open file'],
			'0010-2': [uub.RESULT_ERROR, 'file contains no copyright text block'],
			'0010-3': [uub.RESULT_WARN, 'copyright is outdated'],
			'0010-4': [uub.RESULT_ERROR, 'cannot find copyright line containing year'],
			'0010-5': [uub.RESULT_ERROR, 'file debian/copyright is missing'],
			'0010-6': [uub.RESULT_WARN, 'debian/copyright is not machine-readable DEP-5'],
		}

	def check(self, path):
		""" the real check """
		super(UniventionPackageCheck, self).check(path)

		check_files = []

		# check if copyright file is missing
		fn = os.path.join(path, 'debian', 'copyright')
		try:
			with open(fn, 'r') as stream:
				line = stream.readline().rstrip()
				if line != DEP5:
					self.addmsg('0010-6', 'not machine-readable DEP-5', filename=fn)
		except EnvironmentError:
			self.addmsg('0010-5', 'file is missing', filename=fn)

		# looking for files below debian/
		for f in os.listdir(os.path.join(path, 'debian')):
			fn = os.path.join(path, 'debian', f)
			if f.endswith('.preinst') or f.endswith('.postinst') or f.endswith('.prerm') or f.endswith('.postrm') or \
				f in ['preinst', 'postinst', 'prerm', 'postrm', 'copyright']:
				check_files.append(fn)

		# looking for python files
		for fn in uub.FilteredDirWalkGenerator(path, reHashBang=re.compile('^#!'), readSize=100):
			check_files.append(fn)

		# Copyright (C) 2004-2020 Univention GmbH
		# Copyright (C) 2004-2020 Univention GmbH
		# Copyright 2008 by
		# Copyright: 2004-2020 Univention GmbH
		reCopyrightVersion = re.compile('Copyright(?:\s+\(C\)|:)?\s+([0-9, -]+)\s+(?:by|Univention\s+GmbH)')

		# check files for copyright
		for fn in check_files:
			try:
				content = open(fn, 'r').read()
			except IOError:
				self.addmsg('0010-1', 'failed to open and read file', filename=fn)
				continue
			self.debug('testing %s' % fn)

			if RE_SKIP.search(content):
				continue

			copyright_strings = (
				'under the terms of the GNU Affero General Public License version 3',
				'Binary versions of this',
				'provided by Univention to you as',
				'cryptographic keys etc. are subject to a license agreement between',
				'the terms of the GNU AGPL V3',
				'You should have received a copy of the GNU Affero General Public',
			)

			for teststr in copyright_strings:
				if teststr not in content:
					self.debug('Missing copyright string: %s' % teststr)
					self.addmsg('0010-2', 'file contains no copyright text block', filename=fn)
					break
			else:
				# copyright text block is present - lets check if it's outdated
				match = reCopyrightVersion.search(content)
				if not match:
					self.addmsg('0010-4', 'cannot find copyright line containing year', filename=fn)
				else:
					years = match.group(1)
					current_year = str(time.localtime()[0])
					if current_year not in years:
						self.debug('Current year=%s  years="%s"' % (current_year, years))
						self.addmsg('0010-3', 'copyright line seems to be outdated', filename=fn)
