"""
Solution to Advent of Code 2023 day 10 part 1

Solved by checking valid ajacencies, and then performing BFS on that.
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

mapping = {
	'S': [(0,-1), (0,1), (-1,0), (1,0)],
	'-': [(0,-1), (0,1)],
	'|': [(-1,0), (1,0)],
	'J': [(-1,0), (0,-1)],
	'L': [(-1,0), (0,1)],
	'7': [(1,0), (0,-1)],
	'F': [(1,0), (0,1)],
	'.': [],
}

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#for e in entries:
	#	print(e)

	start = None
	for r,e in enumerate(entries):
		for c,v in enumerate(e):
			if v == 'S':
				start = (r,c)
	
	w,h = len(entries[0]), len(entries)
	
	q = deque([start])
	d = {start:0}
	
	while q:
		i,j = q.pop()
		#print('search', (i,j))
		for ix,jx in mapping[entries[i][j]]:
			if (0 <= i+ix < h) \
				and (0 <= j+jx < w) \
				and (-ix,-jx) in mapping[entries[i+ix][j+jx]] \
				and (i+ix, j+jx) not in d:
				#print('find', (i+ix, j+jx), d[(i, j)] + 1)
				q.appendleft((i+ix, j+jx))
				d[(i+ix, j+jx)] = d[(i, j)] + 1
	#print(d)
	return max(d.values())
				

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

