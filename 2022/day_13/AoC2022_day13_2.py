"""
Solution to Advent of Code 2022 day 13 part 2

Same as part 1, except removing double-newlines, adding in the extra packets for separators. Used functools.cmp_to_key to turn the comparator into a sort key.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage

from collections import Counter, deque
from functools import cache, cmp_to_key


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.replace('\n\n', '\n')
	entries = [json.loads(j) for j in entries.splitlines()]
	#print(entries)

	def comp(l1,l2):
		if isinstance(l1, int) and isinstance(l2, int):
			if l1 < l2:
				return -1
			if l1 > l2:
				return 1
			return None
		elif isinstance(l1, list) and isinstance(l2, list):
			i = 0
			while i < len(l1) and i < len(l2):
				c = comp(l1[i],l2[i])
				if c is not None:
					return c
				i += 1
			if len(l1) == len(l2):
				return None
			if i >= len(l1):
				return -1
			if i >= len(l2):
				return 1
			return None
		elif isinstance(l1, int) and isinstance(l2, list):
			return comp([l1], l2)
		elif isinstance(l1, list) and isinstance(l2, int):
			return comp(l1, [l2])
		
	entries.append([[2]])
	entries.append([[6]])
	
	entries = sorted(entries, key=cmp_to_key(comp))
	
	# Solving
	sol = 1
	for i,n in enumerate(entries):
		if n == [[2]]:
			sol *= i + 1
		if n == [[6]]:
			sol *= i + 1
		
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

