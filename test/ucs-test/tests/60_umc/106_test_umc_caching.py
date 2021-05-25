#!/usr/share/ucs-test/runner /usr/bin/py.test -s
## desc: Test security related HTTP headers are set
## exposure: dangerous
## packages: [univention-management-console-server]

from datetime import timedelta

import pytest
from dateutil.parser import parse

import univention.lib.umc


class TestSecurityHeaders(object):

	@pytest.mark.parametrize('path,expected_cache_control,expires_delta', [
		('management/index.html', 'max-age=604800', timedelta(7)),
		('login/index.html', 'max-age=604800', timedelta(7)),
		('js/dojo/dojo.js', 'max-age=86400', timedelta(1)),
		('js/config.js', 'max-age=0, must-revalidate', None),
		('js/dijit/themes/umc/umc.css', 'max-age=604800', timedelta(7)),
		('languages.json', 'max-age=0, must-revalidate', None),
		('meta.json', 'max-age=0, must-revalidate', None),
		('management/js/umc/modules/udm.js', 'max-age=86400', timedelta(1)),
		('management/js/umc/modules/udm.css', 'max-age=604800', timedelta(7)),
		('management/js/dijit/themes/umc/icons/50x50/udm-users-user.png', 'max-age=2592000', timedelta(30)),
		('management/js/dijit/themes/umc/icons/scalable/udm-users-user.svg', 'max-age=2592000', timedelta(30)),
	])
	def test_login_site(self, path, expected_cache_control, expires_delta):
		client = univention.lib.umc.Client()
		response = client.request('GET', path)
		cache_control = response.get_header('Cache-Control')
		print(path, cache_control)
		date = parse(response.get_header('Date'))
		expires = response.get_header('Expires')
		if expires:
			expires = parse(expires)
		last_modified = response.get_header('Last-Modified')
		if last_modified:
			last_modified = parse(last_modified)

		if expires_delta:
			delta = (expires - date)
			assert delta == expires_delta, (delta, expires_delta)
		assert cache_control == expected_cache_control, (cache_control, expected_cache_control)
