# -*- coding: utf-8 -*-
#
# Copyright (C) 2008-2021 Univention GmbH
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

import os
import re
from email.utils import mktime_tz, parsedate_tz

from debian.changelog import Changelog, ChangelogParseError

import univention.ucslint.base as uub

REticket = re.compile(
	r'''
	(Bug:?[ ]\#[0-9]{1,6} # Bugzilla
	|Issue:?[ ]\#[0-9]{1,6} # Redmine
	|Ticket(\#:[ ]|:?[ ]\#)2[0-9]{3}(0[1-9]|1[0-2])(0[1-9]|[12][0-9]|3[01])(?:1[0-9]{7}|21[0-9]{6})) # OTRS
	(?![0-9]) # not followed by additional digits
	''', re.VERBOSE)
RECENT_ENTRIES = 2


class UniventionPackageCheck(uub.UniventionPackageCheckDebian):

	def getMsgIds(self) -> uub.MsgIds:
		return {
			'0007-1': (uub.RESULT_WARN, 'failed to open file'),
			'0007-2': (uub.RESULT_WARN, 'changelog does not contain ticket/bug/issue number'),
			'0007-3': (uub.RESULT_ERROR, 'debian/changelog entries are not strict-monotonically increasing by time'),
			'0007-4': (uub.RESULT_ERROR, 'debian/changelog entries are not strict-monotonically increasing by version'),
			'0007-5': (uub.RESULT_WARN, 'old debian/changelog entries are not strict-monotonically increasing by time'),
			'0007-6': (uub.RESULT_WARN, 'old debian/changelog entries are not strict-monotonically increasing by version'),
		}

	def check(self, path: str) -> None:
		""" the real check """
		super(UniventionPackageCheck, self).check(path)

		fn = os.path.join(path, 'debian', 'changelog')
		try:
			with open(fn, 'r') as stream:
				changelog = Changelog(stream, strict=True)
		except EnvironmentError as ex:
			self.addmsg('0007-1', 'failed to open and read file: %s' % ex, fn)
			return
		except ChangelogParseError as ex:
			self.addmsg('0007-1', ex, fn)
			return

		for change in changelog[0].changes():
			if REticket.search(change):
				break
		else:
			self.addmsg('0007-2', 'latest changelog entry does not contain bug/ticket/issue number', fn)

		last = None
		for nr, block in enumerate(changelog):
			if last:
				if mktime_tz(parsedate_tz(last.date)) <= mktime_tz(parsedate_tz(block.date)):
					if nr < RECENT_ENTRIES:
						self.addmsg('0007-3', 'not strict-monotonically increasing by time: %s <= %s' % (last.date, block.date), fn)
					else:
						self.addmsg('0007-5', 'old not strict-monotonically increasing by time: %s <= %s' % (last.date, block.date), fn)

				if last.version <= block.version:
					if nr < RECENT_ENTRIES:
						self.addmsg('0007-4', 'not strict-monotonically increasing by version: %s <= %s' % (last.version, block.version), fn)
					else:
						self.addmsg('0007-6', 'old not strict-monotonically increasing by version: %s <= %s' % (last.version, block.version), fn)

			last = block
