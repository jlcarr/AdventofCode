"""
Solution to Advent of Code 2022 day 15 part 2

Solved by looking at the perimeters just outside of each sensor, for each point checking the distances with every other beacon and stopping once a valid solution is found. This turns the 2D problem into a 1D problem.
More elegant solution is to use z3.
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
	entries = [re.findall(r'Sensor at x=(-?\d+), y=(-?\d+): closest beacon is at x=(-?\d+), y=(-?\d+)',e)[0] for e in entries]
	entries = [tuple([int(i) for i in e]) for e in entries]
	#print(entries)

	freq = 4000000
	bound = 4000000
	#bound = 20

	# Solving
	d_list = []
	for i,n in enumerate(entries):
		d = abs(n[0]-n[2]) + abs(n[1]-n[3])
		d_list.append(d)
		
	for i,n in enumerate(entries):
		#print(i)
		d = d_list[i]
		#print('pos', (n[0],n[1]), '->',  (n[2],n[3]), '=', d)
		
		# right-down
		for j in range(d+2):
			x,y = n[0]+d+1-j,n[1]+j
			if 0 <= x <= bound and 0 <= y <= bound \
				and all([abs(n2[0]-x) + abs(n2[1]-y) > abs(n2[0]-n2[2])+abs(n2[1]-n2[3]) for n2 in entries]):
				return freq*x+y
		# down-left
		for j in range(d+2):
			x,y = n[0]-j,n[1]+d+1-j
			if 0 <= x <= bound and 0 <= y <= bound \
				and all([abs(n2[0]-x) + abs(n2[1]-y) > abs(n2[0]-n2[2])+abs(n2[1]-n2[3]) for n2 in entries]):
				return freq*x+y
		# left-up
		for j in range(d+2):
			x,y = n[0]-d-1+j,n[1]-j
			if 0 <= x <= bound and 0 <= y <= bound \
				and all([abs(n2[0]-x) + abs(n2[1]-y) > abs(n2[0]-n2[2])+abs(n2[1]-n2[3]) for n2 in entries]):
				return freq*x+y
		# up-right
		for j in range(d+2):
			x,y = n[0]+j,n[1]-d+1+j
			if 0 <= x <= bound and 0 <= y <= bound \
				and all([abs(n2[0]-x) + abs(n2[1]-y) > abs(n2[0]-n2[2])+abs(n2[1]-n2[3]) for n2 in entries]):
				return freq*x+y
	return None

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

