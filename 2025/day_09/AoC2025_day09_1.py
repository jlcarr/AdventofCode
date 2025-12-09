"""
Solution to Advent of Code 2025 day 9 part 1

Solved using brute forcing all pairs.
A more elegant solution would use using nearest neighbors techniques to find furthest pairs.
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
	entries = [tuple(map(int,e.split(','))) for e in entries]
	#entries = np.array(entries)
	#print(entries)

	# Solving
	sol = 0
	l = len(entries)
	for i,e in enumerate(entries):
		x1,y1 = e
		for j in range(i+1,l):
			x2,y2 = entries[j]
			sol = max(sol, (1+abs(x1-x2))*(1+abs(y1-y2)))
		
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

