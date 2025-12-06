"""
Solution to Advent of Code 2025 day 6 part 1

Solved using Python's split for the nice parsing, and then just some careful looping/indexing.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage
import math

from collections import Counter, deque
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	ops = entries[-1].split()
	entries = [list(map(int,e.split())) for e in entries[:-1]]
	#entries = np.array(entries)
	#print(ops)
	#print(entries)

	# Solving
	sol = 0
	for i,op in enumerate(ops):
		if op == '+':
			sol += sum([e[i] for e in entries])
		else:
			sol += math.prod([e[i] for e in entries])
		
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

