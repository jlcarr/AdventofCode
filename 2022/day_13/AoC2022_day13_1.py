"""
Solution to Advent of Code 2022 day 13 part 1

Solved by implementing the comparator as described. Use the json library to parse the lists.
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
	entries = entries.split('\n\n')
	entries = [[json.loads(j) for j in e.splitlines()] for e in entries]
	#print(entries)

	def comp(l1,l2):
		if isinstance(l1, int) and isinstance(l2, int):
			if l1 < l2:
				return True
			if l1 > l2:
				return False
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
				return True
			if i >= len(l2):
				return False
			return None
		elif isinstance(l1, int) and isinstance(l2, list):
			return comp([l1], l2)
		elif isinstance(l1, list) and isinstance(l2, int):
			return comp(l1, [l2])
		
	# Solving
	sol = 0
	for i,n in enumerate(entries):
		if comp(n[0], n[1]):
			#print(i+1, n[0], n[1])
			sol += i+1
		
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

