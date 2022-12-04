"""
Solution to Advent of Code 2022 day 4 part 1

Solved by simply checking each range to see if it contained the other.
Probably coulda been done more elegantly looping over pairs to check and making one long <= chain
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
	entries = [[[int(j) for j in i.split('-')] for i in e.split(',')] for e in entries]
	#print(entries)

	sol = 0
	for i,n in enumerate(entries):
		if n[0][0] <= n[1][0] and n[0][1] >= n[1][1]:
			sol += 1
		elif n[1][0] <= n[0][0] and n[1][1] >= n[0][1]:
			sol += 1

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

