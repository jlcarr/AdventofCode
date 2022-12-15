"""
Solution to Advent of Code 2022 day 14 part 2

Same as part 1, but widening for more sand dropping, and including the floor bound.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage
from PIL import Image

from collections import Counter, deque
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [[[int(x) for x in p.split(',')] for p in e.split(' -> ')] for e in entries]
	n = max([x for e in entries for p in e for x in p])
	ymax = max([p[1] for e in entries for p in e])
	#print(n, ymax)
	grid = np.zeros((ymax+3,2*n+3), dtype=int)
	for e in entries:
		for p1,p2 in zip(e[:-1],e[1:]):
			if p1[0] == p2[0]:
				s, e = min(p1[1],p2[1]), max(p1[1],p2[1])
				grid[s:e+1, p1[0]] = 1
			elif p1[1] == p2[1]:
				s, e = min(p1[0],p2[0]), max(p1[0],p2[0])
				grid[p1[1], s:e+1] = 1
			#print(p1[0],p2[0]+1,p1[1],p2[1]+1)
		
	#print(grid)
	#img = grid.astype('uint8')*255
	#img[0,500] = 255//2
	#Image.fromarray(img).save('test.png')

	sol = 0
	while True:
		curr = [0, 500]
		while True:
			if curr[0]+1 >= ymax+2:
				grid[tuple(curr)] = 1
				sol += 1
				break
			if grid[curr[0]+1, curr[1]] == 0:
				curr[0] += 1
				continue
			if grid[curr[0]+1, curr[1]-1] == 0:
				curr[0] += 1
				curr[1] -= 1
				continue
			if grid[curr[0]+1, curr[1]+1] == 0:
				curr[0] += 1
				curr[1] += 1
				continue
			grid[tuple(curr)] = 1
			sol += 1
			if curr == [0,500]:
				return sol
			break
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

