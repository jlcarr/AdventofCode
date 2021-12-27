"""
Solution to Advent of Code 2021 day 6 part 1

Solved using Numpy and Scipy's generic filter.
This is probably the most elegant way to solve it, but surprisingly a lot slower than I would have thought.
"""
import time
import sys

import re
import numpy as np
import scipy.ndimage

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries] #+['.']
	#entries.append(['.']*len(entries[0]))
	entries = np.array(entries)

	entries = (entries=='>').astype(int) - (entries=='v').astype(int)

	#entries[:,-1] = entries[:,0]
	#entries[-1,:] = entries[0,:]

	#print(entries)
	#for row in entries:
	#	print(''.join([['.','>','v'][col] for col in row]))

	kern = np.ones((3,3), dtype=int)
	
	def update_filter_east(arr):
		if arr[3+1] == 1 and arr[3+2] == 0:
			return 0
		elif arr[3+1] == 0 and arr[3] == 1:
			return 1
		return arr[3+1]

	def update_filter_south(arr):
		arr = arr.reshape((3,3))
		if arr[1,1] == -1 and arr[2,1] == 0:
			return 0
		elif arr[1,1] == 0 and arr[0,1] == -1:
			return -1
		return arr[1,1]

	def update_filter_identity(arr):
		return arr[3+1]

	sol = 0
	while True:
		sol += 1
		prev = np.copy(entries)
		entries = scipy.ndimage.filters.generic_filter(entries, update_filter_east, footprint=kern, mode='wrap')
		entries = scipy.ndimage.filters.generic_filter(entries, update_filter_south, footprint=kern, mode='wrap')
		if (prev==entries).all():
			break
		#print("step", sol)
		#for row in entries:
		#	print(''.join([['.','>','v'][col] for col in row]))

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

