"""
Solution to Advent of Code 2022 day 15 part 2

Solved using a set of all indices found on the y line, which is filled by started at the nearest point on the y, and moving while within the distance and adding. Finish by removing all actual beacons from the set.
A more elegant solution would have been to use a list of ranges.
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

	y = 2000000

	# Solving
	row_set = set()
	for i,n in enumerate(entries):
		d = abs(n[0]-n[2]) + abs(n[1]-n[3])
		#print('pos', (n[0],n[1]), '->',  (n[2],n[3]), '=', d)
		j = 0
		while abs(j) + abs(n[1]-y) <= d:
			#print('\t', (n[0]+j), (n[0]-j))
			row_set.add(n[0]+j)
			row_set.add(n[0]-j)
			j += 1
	for i,n in enumerate(entries):
		if n[3] == y and n[2] in row_set:
			row_set.remove(n[2])
	#print(row_set)
			
	return len(row_set)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

