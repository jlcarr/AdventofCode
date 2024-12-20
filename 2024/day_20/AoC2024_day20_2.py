"""
Solution to Advent of Code 2024 day 20 part 2

Solved similarly to part 1, except also searching over all cheats of up to 20 Manhattan distance. Note that cheats always take the shortest path between their start and end.
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
	grid = [list(e) for e in entries]
	#print('\n'.join(''.join(e) for e in grid))
	
	# Setup
	m,n = len(grid),len(grid[0])
	start = [(i,j) for i,row in enumerate(grid) for j,c in enumerate(row) if c == 'S'][0]
	end = [(i,j) for i,row in enumerate(grid) for j,c in enumerate(row) if c == 'E'][0]
	
	# Solving
	dists = {start:0}
	curr = start
	while curr != end:
		i,j = curr
		for di,dj in [(1,0), (-1,0), (0,1), (0,-1)]:
			if grid[i+di][j+dj] != '#' and (i+di, j+dj) not in dists:
				dists[(i+di, j+dj)] = dists[(i, j)] + 1
				curr = (i+di, j+dj)
				break
	#print(dists)
	
	cheats = dict()
	for (i,j), cost in dists.items():
		for di in range(-20, 20+1):
			for dj in range(-20, 20+1):
				if abs(di) + abs(dj) > 20:
					continue
				if (0 <= i+di < m) and  (0 <= j+dj < n) and grid[i+di][j+dj] != '#':
					save = dists[(i+di,j+dj)] - dists[(i,j)] - abs(di) - abs(dj)
					if save <= 0:
						continue
					if save not in cheats:
						cheats[save] = []
					cheats[save].append((i,j))
	cheatcounts = {i:len(v) for i,v in cheats.items()}
	#for k in sorted(cheatcounts.keys()):
	#	print(k, cheatcounts[k])
	#print(cheatcounts)
	#print(m,n, m*n)
	return sum(v for k,v in cheatcounts.items() if k >= 100)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

