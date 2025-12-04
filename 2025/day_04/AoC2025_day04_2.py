"""
Solution to Advent of Code 2025 day 4 part 2

Solved similarly to part 1, using numpy with scipy.ndimage.generic_filter to perform the operations on the grid. Sum of array differences is used to check for when the state stops changing, and similarly get the difference with the original array.
More performant solution would have been to keep track of just the updated indices and searched there.
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
	entries = [[int(c=="@") for c in e] for e in entries]
	entries = np.array(entries)
	#print(entries)


	# Solving
	kern = np.ones((3,3), dtype=int)
	#print(kern)
	def conv_func(arr):
		#print(arr.shape)
		arr = arr.reshape((3,3))
		return int(arr.sum()-1 >= 4 and arr[1,1] == 1)
	
	prev_entries = np.ones(entries.shape,dtype=int)
	new_entries = entries
	while np.sum(prev_entries-new_entries) > 0:
		prev_entries = new_entries
		new_entries = scipy.ndimage.generic_filter(prev_entries, conv_func, footprint=kern, mode='constant', cval=0)

	#print(new_entries)
		
	return np.sum(entries-new_entries)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

