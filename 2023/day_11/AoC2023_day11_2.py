"""
Solution to Advent of Code 2023 day 11 part 2

Just kept track of rows and columns which would be expanded, and when computing the distances for each pair, check of any rows or columns between them are in the expanded sets, and if so add on the additional distances.
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
		
	xtimes = 1000*1000-1
	
	nrows = len(entries)
	ncols = len(entries[0])
	
	
	brows = set()
	for r in range(nrows):
		if sum([entries[r][c] == '#' for c in range(ncols)]) == 0:
			brows.add(r)
	
	bcols = set()
	for c in range(ncols):
		if sum([entries[r][c] == '#' for r in range(nrows)]) == 0:
			bcols.add(c)

	gals = []
	for r in range(nrows):
		for c in range(ncols):
			if entries[r][c] == '#':
				gals.append((r,c))
	
	sol = 0
	for (i,j),(ix,jx) in itertools.combinations(gals, 2):
		sol += abs(i-ix) + abs(j-jx)
		for ip in range(min(i,ix), max(i,ix)):
			if ip in brows:
				sol += xtimes
		for jp in range(min(j,jx), max(j,jx)):
			if jp in bcols:
				sol += xtimes
	return sol
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

