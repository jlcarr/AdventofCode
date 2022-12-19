"""
Solution to Advent of Code 2022 day 18 part 1

Solved using a set of all the faces found and all the faces found more than once. The hash key for the face are the block coordinates on either side of the face in sorted order.
More elegant solution would be to use scipy's convolution to count up the faces without neighbors.
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
	entries = [[int(j) for j in e.split(',')] for e in entries]
	#print(entries)

	# Solving
	#kern = np.ones((3), dtype=int)
	#def conv_func(arr):
	#	arr = arr.reshape((3))
	#	return arr[1]
	#entries = scipy.ndimage.filters.generic_filter(entries, conv_func, footprint=kern, mode='constant', cval=0)
	
	face_sets = set()
	recounted = set()
	sol = 0
	for i,n in enumerate(entries):
		# x y z
		for j in [-1,1]:
			side = (n[0]+j, n[1], n[2])
			key = tuple(sorted([side,tuple(n)]))
			if key in face_sets:
				recounted.add(key)
			else:
				face_sets.add(key)
		for j in [-1,1]:
			side = (n[0], n[1]+j, n[2])
			key = tuple(sorted([side,tuple(n)]))
			if key in face_sets:
				recounted.add(key)
			else:
				face_sets.add(key)
		for j in [-1,1]:
			side = (n[0], n[1], n[2]+j)
			key = tuple(sorted([side,tuple(n)]))
			if key in face_sets:
				recounted.add(key)
			else:
				face_sets.add(key)
	return len(face_sets) - len(recounted)
	
if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

