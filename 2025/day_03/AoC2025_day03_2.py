"""
Solution to Advent of Code 2025 day 3 part 2

Solved by realizing we must at least have room for the remaining digits at the end, so for each digit search the slice of candidate positions, which excludes anything before the previous digit was found, and anything after its last possible postion leaving room for the remaining digits.
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
	entries = [[int(c) for c in e] for e in entries]
	#entries = np.array(entries)
	#print(entries)

	# Solving
	sol = 0
	for i,e in enumerate(entries):
		subsol = 0
		pindex = 0
		for j in range(12):
			subrange = e[pindex:len(e)-12+(j+1)]
			maxd = max(subrange)
			index = subrange.index(maxd)
			pindex += index+1
			subsol = 10*subsol + maxd
			#print(subrange, subsol)
		sol += subsol
		#break
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

