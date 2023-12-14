"""
Solution to Advent of Code 2023 day 14 part 1

Iterated over each column, going down the column, and keeping a queue of available places for the rounded rocks to fall, which is reset if we hit a stationary cube rock. After this summing the distances is easy.
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
	#for e in entries:
	#	print(e)
		
	#print('Update')
	rows,cols = len(entries), len(entries[0])
	for c in range(cols):
		rlag = deque([])
		for r in range(rows):
			if entries[r][c] == 'O' and rlag:
				entries[rlag.pop()][c] = 'O'
				entries[r][c] = '.'
				rlag.appendleft(r)
			elif entries[r][c] == '.':
				rlag.appendleft(r)
			elif  entries[r][c] == '#':
				rlag = deque([])
	#for e in entries:
	#	print(e)
	
	sol = 0
	for r in range(rows):
		for c in range(cols):
			if entries[r][c] == 'O':
				sol += rows - r
				
	return sol

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

