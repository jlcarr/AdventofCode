"""
Solution to Advent of Code 2022 day 18 part 2

Solved by first performing a flood-fill via BFS on each block and seeing if doesn't escape. Keeping record of which blocks have already been searched.
More elegant solution would be to use scipy.ndimage.binary_fill_holes.
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
	
	xmax, xmin = max([n[0] for n in entries]), min([n[0] for n in entries])
	ymax, ymin = max([n[1] for n in entries]), min([n[1] for n in entries])
	zmax, zmin = max([n[2] for n in entries]), min([n[2] for n in entries])
	filled = set([tuple(n) for n in entries])
	search_set = set([f for f in filled])
	start = None
	for x in range(xmin, xmax+1):
		for y in range(ymin, ymax+1):
			for z in range(zmin, zmax+1):
				if (x,y,z) not in search_set:
					curr_search_set = set([(x,y,z)])
					seach_queue = deque([(x,y,z)])
					exits = False
					while seach_queue:
						n = seach_queue.pop()
						# x
						for j in [-1,1]:
							if not (xmin <= n[0]+j <= xmax):
								exits = True
								continue
							key = (n[0]+j, n[1], n[2])
							if key not in curr_search_set and key not in filled:
								curr_search_set.add(key)
								seach_queue.appendleft(key)
						# y
						for j in [-1,1]:
							if not (ymin <= n[1]+j <= ymax):
								exits = True
								continue
							key = (n[0], n[1]+j, n[2])
							if key not in curr_search_set and key not in filled:
								curr_search_set.add(key)
								seach_queue.appendleft(key)
						# z
						for j in [-1,1]:
							if not (zmin <= n[2]+j <= zmax):
								exits = True
								continue
							key = (n[0], n[1], n[2]+j)
							if key not in curr_search_set and key not in filled:
								curr_search_set.add(key)
								seach_queue.appendleft(key)
					#if (x,y,z) == (2,2,5):
					#	print(curr_search_set)
					search_set |= curr_search_set
					if not exits:
						filled |= curr_search_set
						
	#print('filled')
	#print(entries)
	#print(filled)
	#print(len(entries), len(filled), filled-set([tuple(e) for e in entries]))
	
	face_sets = set()
	recounted = set()
	sol = 0
	for i,n in enumerate(filled):
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

