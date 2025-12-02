"""
Solution to Advent of Code 2025 day 2 part 1

Solved by going through numbers until concatenating them surpasses the largest range, thereby only searching the square root's worth. Checked all ranges linearly.
More elegant solution would be to sort the ranges, assuming/checking they don't overlap, run through them linearly as we count up numbers to check.
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
	entries = ''.join(entries)
	#entries = [int(e) for e in entries]
	entries = entries.split(',')
	entries = [tuple(map(int,e.split('-'))) for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	#entries = np.array(entries)
	#print(entries)

	maxv = max([e[1] for e in entries])
	#print(maxv)

	# Solving
	sol = 0
	i = 1
	while (v := int(str(i)*2)) < maxv:
		for l,h in entries:
			if v >= l and v <= h:
				sol += v
				break
		i += 1

	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

