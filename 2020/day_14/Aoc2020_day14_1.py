"""
Solution to Advent of Code 2020 day 14 part 1

Bit-string conversion and manipulation
"""
import time
import sys

import re

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	mem = dict()
	mask = ['X']*36
	entries = entries.splitlines()
	for e in entries:
		if e.startswith('mask'):
			mask = list(e.split('= ')[1])
			#print(mask)
		if e.startswith('mem'):
			#print(e)
			x,y = re.match(r'mem\[(\d+)\] = (\d+)',e).groups()
			x = int(x)
			y = int(y)
			#print(x,y,bin(y)[2:].zfill(36))
			y = bin(y)[2:].zfill(36)
			y = ''.join([d if m=='X' else m for d,m in zip(y,mask) ])
			y = int(y,2)
			mem[x] = y
			#print(y)

	return sum(mem.values())


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
