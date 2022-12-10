"""
Solution to Advent of Code 2022 day 10 part 1

Solved using modular arithmetic to check when at the correct instruction, and fully simulating every cycle.
More elegant solution would probably to avoid writing the same updating code twice.
"""
import time
import sys

# tools
import re

import numpy as np
import scipy.ndimage

from collections import Counter
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [('addx', int(e.split(' ')[1])) if e != 'noop' else (e,) for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	#print(entries)

	entries = entries[::-1]

	# Solving
	sol = 0
	x = 1
	i = 0
	while entries:
		ins = entries.pop()
		if ins[0] == 'noop':
			i += 1
			if (i-20)%40 == 0:
				sol += i * x
				#print(sol, i, x, i*x)
			#print(i, x)
		elif ins[0] == 'addx':
			for j in range(2):
				i += 1
				if (i-20)%40 == 0:
					sol += i * x
					#print(sol, i, x, i*x)
				#print(i, x)
			x += ins[1]
	#print(i+1, x)
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

