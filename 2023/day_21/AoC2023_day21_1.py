"""
Solution to Advent of Code 2023 day 21 part 1

Simply perform the simulation with BFS. Convolution is another possible approach.
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
	#print(entries)

	rows,cols = len(entries), len(entries[0])

	start = None
	for i in range(rows):
		for j in range(cols):
			if entries[i][j] == 'S':
				start = (i,j)
				break
	#print(start)
	q = [start]

	for steps in range(64):
		newq = []
		newqset = set()
		for i,j in q:
			for ip,jp in [(i+1,j),(i-1,j),(i,j+1),(i,j-1)]:
				if (0 <= ip < rows) and (0 <= j < cols) and (ip,jp) not in newqset and entries[ip][jp] != '#':
					newq.append((ip,jp))
					newqset.add((ip,jp))
		q = newq

	return len(q)

	# conv template
	kern = np.ones((3,3), dtype=int)
	def conv_func(arr):
		arr = arr.reshape((3,3))
		return arr[1,1]
	entries = scipy.ndimage.filters.generic_filter(entries, conv_func, footprint=kern, mode='constant', cval=0)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

