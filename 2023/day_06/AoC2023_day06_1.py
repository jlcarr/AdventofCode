"""
Solution to Advent of Code 2023 day 6 part 1

Solved by simply running through each possible speed and checking if it wins. A more elegant solution using math is explained in part 2.
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
	ts,ds = entries.splitlines()
	ts = list(map(int,ts.split(':')[1].split()))
	ds = list(map(int, ds.split(':')[1].split()))

	# Solving
	#print(ts,ds)
	sol = 1
	for t,d in zip(ts,ds):
		s = 0
		for i in range(t):
			myd = i * (t-i)
			if myd > d:
				s += 1
		#print(s)
		sol *= s
	#print(sol)
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

