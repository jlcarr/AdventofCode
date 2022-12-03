"""
Solution to Advent of Code 2022 day 3 part 2

Solved by going 3 at a time, and taking the set intersection between all, finishing with the same ordinal arithmatic.
More elegant solution would be to you a 3-stepped for-loop, also no need to put all intersections on 1 line.
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
	#print(entries)

	# Solving
	sol = 0
	i = 0
	while i < len(entries):
		res = set(entries[i]).intersection(set(entries[i+1])).intersection(set(entries[i+2]))
		#print(res)
		res = list(res)[0]
		if ord('a') <= ord(res) <= ord('z'):
			sol += ord(res) - ord('a') + 1
		if ord('A') <= ord(res) <= ord('Z'):
			sol += ord(res) - ord('A') + 27
		i += 3

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

