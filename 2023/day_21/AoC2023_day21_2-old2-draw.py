"""
Solution to Advent of Code 2023 day 21 part 2

Solved using numpy
More elegant solution
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
	entries = [list(e) for e in entries]
	#entries = np.array(entries)
	print(entries)

	rows,cols = len(entries), len(entries[0])

	start = None
	for i in range(rows):
		for j in range(cols):
			if entries[i][j] == 'S':
				start = (i,j)
				break
	print(start)
	
	n_mcomplete = sum(int(c != '#') for row in entries for c in row)
	mcomplete = set()
	
	tol = n_mcomplete
	same_counter = {(0,0):(1,1)}
	fixed = set()
	
	q = {(0,0): set([start])}

	for steps in range(500):
		newq = dict()
		#print(steps, len(q), len(mcomplete))
		for mi,mj in q.keys():
			for (i,j) in q[(mi,mj)]:
				for ip,jp in [(i+1,j),(i-1,j),(i,j+1),(i,j-1)]:
					mip,mjp = mi,mj
					# fix map piece
					if ip < 0:
						mip -= 1
					if ip >= rows:
						mip += 1
					if jp < 0:
						mjp -= 1
					if jp >= cols:
						mjp += 1
					# fix coords
					ip %= rows
					jp %= cols
					# dont take rocks
					if entries[ip][jp] == '#':
						continue
					# pass if complete
					#if (mip,mjp) in mcomplete:
					#	continue
					
					# add if not there
					if (mip,mjp) not in newq:
						newq[(mip,mjp)] = set()
					# finally add
					newq[(mip,mjp)].add((ip,jp))
		q = newq
		# filter out completes
		for k in list(q.keys()):
			if len(q[k]) == n_mcomplete:
				mcomplete.add(k)
				del q[k]
			#print('k',k, len(q[k]))
		for rr in range(rows):
				print(''.join('O' if (rr,cc) in q[(0,0)] else entries[rr][cc] for cc in range(cols)))
		print(len(q[(0,0)]), n_mcomplete//2)
	# add lru
	print(n_mcomplete)
	return sum(len(v) for v in q.values()) + n_mcomplete * len(mcomplete)

	# Solving
	kern = np.ones((3), dtype=int)
	def conv_func(arr):
		arr = arr.reshape((3))
		return arr[1]
	entries = scipy.ndimage.filters.generic_filter(entries, conv_func, footprint=kern, mode='constant', cval=0)
	
	sol = 0
	for i,n in enumerate(entries):
		sol += 1
		

	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

