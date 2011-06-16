#!/usr/bin/python2.6
# -*- coding: utf-8 -*-
#
# Univention Management Console
#  wizard: nagios configuration
#
# Copyright 2007-2011 Univention GmbH
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

import univention.management.console as umc
import univention.management.console.protocol as umcp
import univention.management.console.handlers as umch
import univention.management.console.dialog as umcd
import univention.management.console.tools as umct

import univention.debug as ud
import univention_baseconfig as ub

import notifier
import notifier.popen

import os, re

import _revamp

_ = umc.Translation( 'univention.management.console.wizards.nagios' ).translate

icon = 'wizards/nagios/module'
short_description = _( 'Nagios' )
long_description = _( 'Nagios configuration' )
categories = [ 'wizards' ]

command_description = {
	'wizard/nagios/show': umch.command(
		short_description = _( 'Nagios' ),
		long_description = _( 'View Nagios configuration' ),
		method = 'nagios_show',
		values = {},
		startup = True,
		priority = 100
	),
	'wizard/nagios/set': umch.command(
		short_description = _( 'Nagios' ),
		long_description = _( 'Set Nagios configuration' ),
		method = 'nagios_set',
		values = { 'number' : umc.String( _( 'Phone number' ) ), },
	),
}

class handler( umch.simpleHandler, _revamp.Web ):
	def __init__( self ):
		global command_description
		umch.simpleHandler.__init__( self, command_description )
		_revamp.Web.__init__( self )

	def nagios_show( self, object ):
		umc.baseconfig.load()
		self.finished( object.id(), { 'number' : umc.baseconfig.get( 'nagios/server/smsrecipient', 0 ), } )

	def nagios_set( self, object ):
		ub.handler_set( [ 'nagios/server/smsrecipient=%s' % object.options[ 'number' ] ] )
		self.finished( object.id(), {} )
