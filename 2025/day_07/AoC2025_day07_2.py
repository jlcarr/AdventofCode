"""
Solution to Advent of Code 2025 day 7 part 2

Solved similarly to part 1, but aggregating counts of paths into the new row.
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
	#entries = np.array(entries)
	#print(entries)

	# Solving
	#kern = np.ones((3), dtype=int)
	#def conv_func(arr):
	#	arr = arr.reshape((3))
	#	return arr[1]
	#entries = scipy.ndimage.generic_filter(entries, conv_func, footprint=kern, mode='constant', cval=0)
	
	l = len(entries[0])
	prev = [0] * l
	sol = 0
	for i,e in enumerate(entries):
		row = [0] * l
		for j,c in enumerate(e):
			if c == 'S':
				row[j] = 1
			if c == '^' and prev[j]:
				#print(i,j)
				if j-1 >= 0:
					row[j-1] += prev[j]
				if j + 1 < l:
					row[j+1] += prev[j]
			if c == '.' and prev[j]:
				row[j] += prev[j]
		prev = row
		#print(prev)
		
	return sum(prev)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

