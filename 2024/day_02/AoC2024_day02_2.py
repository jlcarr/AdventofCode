"""
Solution to Advent of Code 2024 day 2 part 2

Similar to part 1, except also looping over all elements to slice out for each row.
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
	entries = [[int(c) for c in e.split()] for e in entries]
	
	sol = 0
	for e in entries:
		for i in range(len(e)):
			d = np.diff(e[:i]+e[i+1:])
			if (np.all(d < 0) or np.all(d > 0)) and ((1 > np.abs(d)).sum() + (np.abs(d) > 3).sum() == 0):
				sol += 1
				break
	return sol
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

