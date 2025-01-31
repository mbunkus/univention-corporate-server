#!/usr/share/ucs-test/runner /usr/bin/py.test-3 -s
## desc: Test security related HTTP headers are set
## exposure: dangerous
## packages: [univention-management-console-server]

import pytest
import copy
from collections import defaultdict
from univention.testing import utils, network
from six.moves.http_client import HTTPConnection


class TestSecurityHeaders(object):

	@pytest.mark.parametrize('path', [
		'login/',
		'login/index.html',
		'login/blank.html',
		'login/login.html',
	])
	def test_login_site(self, path, Client):
		client = Client()
		response = client.request('GET', path)
		assert response.get_header("X-Frame-Options") is None  # changed from: == "SAMEORIGIN"
		assert response.get_header("Content-Security-Policy") == "default-src 'self' 'unsafe-inline' 'unsafe-eval'  https://www.piwik.univention.de/ ; frame-ancestors 'self';"

		assert response.get_header("X-Permitted-Cross-Domain-Policies") == "master-only"
		assert response.get_header("X-XSS-Protection") == "1; mode=block"
		assert response.get_header("X-Content-Type-Options") == "nosniff"

	@pytest.mark.parametrize('path', [
		'/languages.json',
		'/portal/',
		'/management/',
	])
	def test_univention(self, path, ucr, Client):
		client = Client()
		response = client.request('GET', path)
		assert response.get_header("X-Permitted-Cross-Domain-Policies") == "master-only"
		assert response.get_header("X-XSS-Protection") == "1; mode=block"
		assert response.get_header("X-Content-Type-Options") == "nosniff"
		assert response.get_header("X-Frame-Options") is None  # changed from: == "DENY"
		if path == '/languages.json':
			assert response.get_header("Content-Security-Policy") == "frame-ancestors 'none';"
		else:
			expected = "frame-ancestors 'self' https://%(ucs/server/sso/fqdn)s/ http://%(ucs/server/sso/fqdn)s/;" % defaultdict(lambda: '', ucr)
			assert expected in response.get_header("Content-Security-Policy")

	@pytest.mark.xfail(reason='Bug #52940')
	def test_ip_bound_to_session(self, Client, Unauthorized, ucr, restart_umc_server):
		client = Client('%s.%s' % (ucr.get('hostname'), ucr.get('domainname')))
		client.ConnectionType = HTTPConnection  # workaround TLS hostname mismatch

		account = utils.UCSTestDomainAdminCredentials()
		client.authenticate(account.username, account.bindpw)
		# make sure any UMC module is present (the session is not dropped to anonymous)
		assert any(x['id'] == 'top' for x in client.umc_get('modules').data['modules'])

		# change the external IP address
		with network.NetworkRedirector() as nethelper:
			nethelper.add_loop('1.2.3.4', '4.3.2.1')
			c = Client('1.2.3.4')
			c.ConnectionType = HTTPConnection  # workaround TLS hostname mismatch
			c.cookies = copy.deepcopy(client.cookies)
			with pytest.raises(Unauthorized) as exc:
				c.umc_get('modules')
			assert 'The current session is not valid with your IP address for security reasons.' in exc.value.message

			# check if the session is still bound after the internal connection to the UMC-Server was lost
			restart_umc_server()
			c.cookies = copy.deepcopy(client.cookies)
			with pytest.raises(Unauthorized) as exc:
				c.umc_get('modules')
			assert 'The current session is not valid with your IP address for security reasons.' in exc.value.message

		# make sure any UMC module is present (the session is not dropped to anonymous)
		assert any(x['id'] == 'top' for x in client.umc_get('modules').data['modules'])

		# make sure the same rules apply for localhost
		c2 = Client('localhost')
		c2.ConnectionType = HTTPConnection  # workaround TLS hostname mismatch
		c2.cookies = copy.deepcopy(client.cookies)
		assert any(x['id'] == 'top' for x in c2.umc_get('modules').data['modules'])

		# check if the session is still bound after the internal connection to the UMC-Server was lost
		restart_umc_server()
		c2.cookies = copy.deepcopy(client.cookies)
		assert any(x['id'] == 'top' for x in c2.umc_get('modules').data['modules'])

		# make sure any UMC module is present (the session is not dropped to anonymous)
		assert any(x['id'] == 'top' for x in client.umc_get('modules').data['modules'])
