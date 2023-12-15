"""
Solution to Advent of Code 2023 day 15 part 1

Solved by simply iterating through the string, and applying the operations, using Python's ord to get the ASCII values.
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
	entries = entries.replace('\n', '')

	# Parsing
	entries = entries.split(',')
	#print(entries)

	# Solving

	sol = 0
	for i,e in enumerate(entries):
		curr = 0
		for c in e:
			curr += ord(c)
			curr *= 17
			curr %= 256
		
		sol += curr
		
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

