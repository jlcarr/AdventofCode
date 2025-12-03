"""
Solution to Advent of Code 2025 day 3 part 1

Solved using max and index to find the first occurrence of the maximum digit, then if it's not at the end, take the largest digit in the array sliced to the right, otherwise take the largest digit in the rest of the array.
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
	entries = [[int(c) for c in e] for e in entries]
	#entries = np.array(entries)
	#print(entries)

	# Solving
	sol = 0
	for i,e in enumerate(entries):
		maxv = max(e)
		index = e.index(maxv)
		if index == len(e) - 1:
			max2 = max(e[:-1])
			sol += 10*max2 + maxv
		else:
			max2 = max(e[index+1:])
			sol += 10*maxv + max2
		
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

