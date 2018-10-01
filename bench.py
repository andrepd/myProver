from pathlib import Path
# from os import system
import subprocess

command = '/usr/bin/time -f "{fname} %e %U %S"  --output=bench.txt -a ./main.native <{fname} >/dev/null 2>/dev/null'
folder = './inputs'

for i in Path(folder).iterdir():
	print(i)
	# system(command.format(fname=i))
	try:
		subprocess.run([command.format(fname=i)], shell=True, timeout=10)
	except subprocess.TimeoutExpired:
		print('Timeout')
	# print(i)
