"""
Solution to Advent of Code 2022 day 3 part 1

Solved by slicing each string in half, then taking the intersection of the sets of each half, and finally performing ordinal arithmetic on the resulting character.
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

	sol = 0
	for i,n in enumerate(entries):
		l =len(n)//2
		res = set(n[:l]).intersection(set(n[l:]))
		#print(res)
		res = list(res)[0]
		if ord('a') <= ord(res) <= ord('z'):
			sol += ord(res) - ord('a') + 1
		if ord('A') <= ord(res) <= ord('Z'):
			sol += ord(res) - ord('A') + 27

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

