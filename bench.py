from pathlib import Path
# from os import system
import subprocess
from sys import argv, stderr

command = '/usr/bin/time -f "{fname} %e %U %S"  --output={outname} -a ./main.native <{fname} >/dev/null 2>/dev/null'
folder = './inputs'

if len(argv) != 2:
	print(f'Usage: ./{argv[0]} out_filename', file=stderr)
	exit(1)

outname = argv[1]

for i in Path(folder).iterdir():
	print(i)
	# system(command.format(fname=i))
	try:
		subprocess.run([command.format(fname=i, outname=outname)], shell=True, timeout=10)
	except subprocess.TimeoutExpired:
		print('Timeout')
	# print(i)
