"""
Solution to Advent of Code 2025 day 1 part 2

Solved by converting the L rotations to negative, using an accumulator and modular arithmetic.
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
	entries = [int(e[1:]) * (-1 if e[0] == 'L' else 1) for e in entries]
	#entries = np.array(entries)
	#print(entries)

	acc = 50
	sol = 0
	for i,n in enumerate(entries):
		acc = (acc + n) % 100
		sol += acc == 0
		
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

