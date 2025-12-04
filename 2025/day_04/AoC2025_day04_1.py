"""
Solution to Advent of Code 2025 day 4 part 1

Solved using numpy with scipy.ndimage.generic_filter to make an array with indicators where rolls would be removed, which can be summed for the final answer.
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
		return int(arr.sum()-1 < 4 and arr[1,1] == 1)
	entries = scipy.ndimage.generic_filter(entries, conv_func, footprint=kern, mode='constant', cval=0)
	
	#print(entries)
		
	return entries.sum()


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

