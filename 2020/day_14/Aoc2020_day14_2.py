"""
Solution to Advent of Code 2020 day 14 part 2

Bit-string manipulation and conversion and counting in binary
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
			x = bin(x)[2:].zfill(36)
			
			l = len([m for m in mask if m == 'X'])
			for i in range(2**l):
				m_float = list(bin(i)[2:].zfill(l))
				#print(mask,m_float,x)
			
				x_temp = ''.join([m_float.pop() if m=='X' else ('1' if m=='1' else d) for d,m in zip(x,mask)])
				x_temp = int(x_temp,2)
				mem[x_temp] = y
			#print(y)

	return sum(mem.values())


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
