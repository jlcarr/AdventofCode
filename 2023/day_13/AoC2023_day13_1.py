"""
Solution to Advent of Code 2023 day 13 part 1

Used numpy with indexing to compare vertical and horizontal mirrors about different candidate lines, being careful for bounds.
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
	entries = entries.split('\n\n')
	entries = [list(map(list,e.splitlines())) for e in entries]
	entries = [(np.array(e) == '#').astype(int) for e in entries]
	#for e in entries:
	#	print(e)
		
	row_mirrors = []
	col_mirrors = []
	for i,e in enumerate(entries):
		#print('entry', i)
		#print(e)
		for row in range(1,e.shape[0]):
			if row+row < e.shape[0]:
				#print(True, row, row+row)
				#print(e[:row, :])
				#print(e[row:row+row, :])
				if np.all(e[:row, :] == e[row:row+row, :][::-1,:]):
					row_mirrors.append(row)
					#print('rowx', row)
			else:
				#print(False, row, 2*row-e.shape[0])
				#print(e[2*row-e.shape[0]:row, :])
				#print(e[row:, :])
				if np.all(e[2*row-e.shape[0]:row, :] == e[row:, :][::-1,:]):
					row_mirrors.append(row)
					#print('row', row)
					
		for col in range(1,e.shape[1]):
			if col+col < e.shape[1]:
				#print(True, col, col+col)
				#print(e[:, :col])
				#print(e[:, col:col+col][:,::-1])
				#print(e[:, :col] == e[:, col:col+col][:,::-1])
				if np.all(e[:, :col] == e[:, col:col+col][:,::-1]):
					col_mirrors.append(col)
					#print('colx', col)
			else:
				if np.all(e[:, 2*col-e.shape[1]:col] == e[:, col:][:,::-1]):
					col_mirrors.append(col)
					#print('col', col)
	#print(row_mirrors)
	#print(col_mirrors)

	return sum(col_mirrors) + 100*sum(row_mirrors)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

