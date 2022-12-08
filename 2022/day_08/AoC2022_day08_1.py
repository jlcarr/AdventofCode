"""
Solution to Advent of Code 2022 day 8 part 2

Simply performed the looping on each element for each direction. Careful of off-by-one errors!
More elegant solution using np.maximum.accumulate is possible, but have to be careful of off-by-ones and padding.
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
	entries = [[int(i) for i in e] for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	entries = np.array(entries)
	#print(entries)
	
	#print()
	
	res = np.zeros(entries.shape, dtype=bool)
	#print(res)

	n,m = entries.shape
	for i in range(n):
		curr_max = -1
		for j in range(m):
			res[i,j] = res[i,j] or entries[i,j] > curr_max
			curr_max = max(curr_max, entries[i,j])
	for i in range(n):
		curr_max = -1
		for j in range(m-1,-1,-1):
			res[i,j] = res[i,j] or entries[i,j] > curr_max
			curr_max = max(curr_max, entries[i,j])
	for j in range(m):
		curr_max = -1
		for i in range(n):
			res[i,j] = res[i,j] or entries[i,j] > curr_max
			curr_max = max(curr_max, entries[i,j])
	for j in range(m):
		curr_max = -1
		for i in range(n-1,-1,-1):
			res[i,j] = res[i,j] or entries[i,j] > curr_max
			curr_max = max(curr_max, entries[i,j])

	return res.sum()

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

