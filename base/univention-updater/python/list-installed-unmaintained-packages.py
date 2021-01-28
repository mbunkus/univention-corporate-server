#/usr/bin/python3

import apt
import sys

MAINTAINED_PACKAGES = '/usr/share/univention-errata/univention-maintained-packages.txt'


def get_installed_packages():
	cache = apt.Cache()
	return [package.name for package in cache if cache[package.name].is_installed]


def main():
	try:
		with open(MAINTAINED_PACKAGES) as fd:
			installed_unmaintained_packages = list(set(get_installed_packages()) - set(fd.read().splitlines()))
			print(installed_unmaintained_packages)
	except FileNotFoundError as exc:
		print(f'{MAINTAINED_PACKAGES} does not exist', file=sys.stderr)
		sys.exit(1)


if __name__ == '__main__':
	main()
