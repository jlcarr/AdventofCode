"""
Solution to Advent of Code 2021 day 9 part 1

Solved by simply iterating over the array and checking neighbors.
More elegant solution using numpy:
inport scipy.ndimage
kern = np.array([
	[0,1,0],
	[1,1,1],
	[0,1,0],
])
min_mask = scipy.ndimage.filters.generic_filter(entries, np.min, footprint=kern) == entries
return np.sum(entries*min_mask.astype(int))
"""
import time
import sys

import re
import numpy as np
from scipy import signal

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	entries = [[int(i) for i in e] for e in entries]
	entries = np.array(entries, dtype=int)
	#print(entries)

	sol = 0
	count = 0
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
				sol += entries[i,j] +1
				count +=1
	#print(count)
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

