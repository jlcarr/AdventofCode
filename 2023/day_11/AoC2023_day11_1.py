"""
Solution to Advent of Code 2023 day 11 part 1

Solved by simply performing the array expansion as we check each row and column for empties, then summing every pairwise distance.
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
import itertools
import math

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#print(entries)
	#for e in entries:
	#	print(e)
	
	nrows = len(entries)
	ncols = len(entries[0])
	
	temp = []
	for r in range(nrows):
		temp.append(entries[r][:])
		if sum([entries[r][c] == '#' for c in range(ncols)]) == 0:
			temp.append(entries[r][:])
	entries = temp
	nrows = len(entries)
	
	temp = [[] for r in range(nrows)]
	for c in range(ncols):
		for r in range(nrows):
			temp[r].append(entries[r][c])
		if sum([entries[r][c] == '#' for r in range(nrows)]) == 0:
			for r in range(nrows):
				temp[r].append(entries[r][c])
	entries = temp
	ncols = len(entries[0])
	#for e in entries:
	#	print(e)

	gals = []
	for r in range(nrows):
		for c in range(ncols):
			if entries[r][c] == '#':
				gals.append((r,c))
	
	sol = 0
	for (i,j),(ix,jx) in itertools.combinations(gals, 2):
		sol += abs(i-ix) + abs(j-jx)
	return sol
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

