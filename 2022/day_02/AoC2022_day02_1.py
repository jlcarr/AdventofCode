"""
Solution to Advent of Code 2022 day 2 part 1

Solved by constructing the map of both inputs the the winning points, then if-statement for shape points.
More elegant solution would have been to combind the two, so no ifstatements needed.
"""
import time
import sys

# tools
import re

import numpy as np
import scipy.ndimage

from collections import Counter
from functools import cache

scores = {
	'A': {'X': 3, 'Y': 6, 'Z': 0},
	'B': {'X': 0, 'Y': 3, 'Z': 6},
	'C': {'X': 6, 'Y': 0, 'Z': 3}
}

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [e.split(' ') for e in entries]
	#print(entries)

	sol = 0
	for i,n in enumerate(entries):
		if n[1] == 'X':
			sol += 1
		if n[1] == 'Y':
			sol += 2
		if n[1] == 'Z':
			sol += 3
		sol += scores[n[0]][n[1]]
		

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

