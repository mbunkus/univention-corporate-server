#/usr/bin/python3

import os
import apt
import sys
import textwrap

MAINTAINED_PACKAGES = '/usr/share/univention-errata/univention-maintained-packages.txt'


def get_installed_packages():
	cache = apt.Cache()
	return [package.name for package in cache if cache[package.name].is_installed]


def main():
	size = os.get_terminal_size()
	try:
		with open(MAINTAINED_PACKAGES) as fd:
			installed_unmaintained_packages = list(set(get_installed_packages()) - set(fd.read().splitlines()))
			if installed_unmaintained_packages:
				print('The following packages are unmaintained:')
				text = ' '.join(installed_unmaintained_packages)
				for line in textwrap.wrap(text, width=int(size.columns - 20), break_long_words=False, break_on_hyphens=False):
					print('  ' + line)
				sys.exit(1)
	except FileNotFoundError:
		print(f'{MAINTAINED_PACKAGES} does not exist', file=sys.stderr)
		sys.exit(1)


if __name__ == '__main__':
	main()
