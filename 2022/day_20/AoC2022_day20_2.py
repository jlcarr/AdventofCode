"""
Solution to Advent of Code 2022 day 20 part 2

Same as part 1, but applying the extra transformations keeping track of the very original positions. Extra care with the modular arithmetic.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage

from collections import Counter, deque
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [int(e) for e in entries]
	#entries = [1, 2, -3, 3, -2, 0, 4]
	#print(entries)
	print(min(entries), max(entries), len(entries), len(set(entries)))

	# Solving
	n = len(entries)
	
	entries = [e*811589153 for e in entries]
	
	def mix(entries, order):
		n = len(entries)
		for i in range(n):
			index = order.index(i)
			j = order.pop(index)
			v = entries.pop(index)
			new_index = index+v
			if new_index <= 0:
				k = -new_index // (n - 1)
				new_index += k * (n - 1)
			while new_index <= 0:
				new_index += n - 1
			if new_index >= n:
				k = new_index // (n - 1)
				new_index -= k * (n - 1)
			while new_index >= n:
				new_index += - n + 1
			order.insert(new_index, j)
			entries.insert(new_index, v)
			#print(v, entries, index+v, new_index)
		return entries
		
	mixed = entries
	order = list(range(n))
	for i in range(10):
		mixed = mix(mixed, order)
	#print(mixed)

	sol = 0
	zeroindex = mixed.index(0)
	for i in range(1,3+1):
		sol += mixed[(i*1000+zeroindex)%n]
		print(mixed[(i*1000+zeroindex)%n])
		#print((i*1000 + zeroindex)%n)
		#break

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

