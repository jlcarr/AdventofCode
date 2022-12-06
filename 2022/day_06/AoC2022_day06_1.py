"""
Solution to Advent of Code 2022 day 6 part 1

Solved using sets to check for uniqueness in the rolling window.
A more elegant approach would have been to use array slicing. Also a rolling window woulda been more efficient.
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
	# None
	#print(entries)

	for i,n in enumerate(entries):
		if i + 4-1 >= len(entries):
			break
		#print(i,[entries[i+j] for j in range(4)])
		if len(set([entries[i+j] for j in range(4)])) == 4:
			return i+4
		
	return None

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

