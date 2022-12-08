"""
Solution to Advent of Code 2022 day 8 part 2

Simply performed the looping on each element for each direction. Careful of off-by-one errors!
I don't think a more elegant numpy solution exists, but I wonder if an O(n^2) solution exists using monotonic stacks.
"""
import time
import sys

# tools
import re

import numpy as np
import scipy.ndimage

from collections import Counter
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [[int(i) for i in e] for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	entries = np.array(entries)
	#print(entries)
	
	#print()
	
	res = np.zeros(entries.shape)

	result = 0
	n,m = entries.shape
	for i in range(n):
		for j in range(m):
			#print(i,j)
			sol = 1
			
			temp = 0
			ix = i
			while ix > 0:
				ix -= 1
				temp += 1
				if entries[ix,j] >= entries[i,j]:
					break
			sol *= max(1, temp)
			#print(temp)
			
			temp = 0
			ix = i
			while ix < m-1:
				ix += 1
				temp += 1
				if entries[ix,j] >= entries[i,j]:
					break
			sol *= max(1, temp)
			#print(temp)
			
			temp = 0
			jx = j
			while jx > 0:
				jx -= 1
				temp += 1
				if entries[i,jx] >= entries[i,j]:
					break
			sol *= max(1, temp)
			#print(temp)
			
			temp = 0
			jx = j
			while jx < n-1:
				jx += 1
				temp += 1
				if entries[i,jx] >= entries[i,j]:
					break
			sol *= max(1, temp)
			#print(temp)
			
			#print(sol)
			#print()
			res[i,j] = sol
			result = max(sol, result)
	#print(res)
	return result

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
