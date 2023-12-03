"""
Solution to Advent of Code 2023 day 3 part 2

Similar to part 1, except keep track of all gears by their positions, and during scans over a number keep a set of all adjacent gears, at boundary add to that gear's list of ratios, which can then be accumulated at the end.
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
	#print(entries)
	
	rows, cols = len(entries), len(entries[0])
	gears = dict()
	for i in range(rows):
		num = ''
		gearset = set()
		for j in range(cols):
			if entries[i][j] in '0123456789':
				num += entries[i][j]
				for ix in [i-1,i,i+1]:
					for jx in [j-1,j,j+1]:
						if (0 <= ix < rows) and (0 <= jx < cols) and (entries[ix][jx] == '*'):
							gearset.add((ix,jx))
			else:
				if gearset and num:
					#print(gearset, num)
					for g in gearset:
						if g not in gears:
							gears[g] = []
						gears[g].append(int(num))
				gearset = set()
				num = ''
		if gearset and num:
			#print(gearset, num)
			for g in gearset:
				if g not in gears:
					gears[g] = []
				gears[g].append(int(num))
		partnum = False
	#print(gears)
	sol = 0
	for g,ratios in gears.items():
		if len(ratios) > 1:
			ratio = 1
			for r in ratios:
				ratio *= r
			sol += ratio
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

