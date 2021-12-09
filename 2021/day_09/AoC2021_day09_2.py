"""
Solution to Advent of Code 2021 day 9 part 2

Solved using skimage's food function. Mathematical morphology functions are often useful for topograpical data.
More elegant approach would have been to use a better technique for part 1.
"""
import time
import sys

import re
import numpy as np
from skimage.morphology import flood

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	entries = [[int(i) for i in e] for e in entries]
	entries = np.array(entries, dtype=int)
	#print(entries)

	kern = np.array([
		[0,1,0],
		[1,1,1],
		[0,1,0],
	])

	# finding the low points
	points = []
	for i in range(entries.shape[0]):
		for j in range(entries.shape[1]):
			is_risk = True
			if i>0 and entries[i-1,j] <= entries[i,j]:
				is_risk = False
			if i<entries.shape[0]-1 and entries[i+1,j] <= entries[i,j]:
				is_risk = False
			if j>0 and entries[i,j-1] <= entries[i,j]:
				is_risk = False
			if j<entries.shape[1]-1 and entries[i,j+1] <= entries[i,j]:
				is_risk = False
			if is_risk:
				points.append((i,j))
	#print(points)

	# Get the top ridges then flood starting from each low point
	segment = 9*(entries == 9).astype(int)
	basins = []
	for point in points:
		flooded = flood(segment, point, footprint=kern)
		basins.append(np.sum(flooded))
	#print(segment)
	#print(flooded)
	#print(np.sum(flooded))

	# Compute the final solution
	basins.sort()
	sol = 1
	for b in basins[-3:]:
		sol *= b

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

