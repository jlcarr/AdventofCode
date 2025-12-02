"""
Solution to Advent of Code 2025 day 2 part 2

Solved similarly to part 1, but with a loop over multiples of concatenation, but to the maximum of the largest range end's length. Used a set to avoid double-counting.
More elegant solution would have been to check each number found cannot be made of a smaller concatenated unit, and also the faster range check.
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
	entries = ''.join(entries)
	#entries = [int(e) for e in entries]
	entries = entries.split(',')
	entries = [tuple(map(int,e.split('-'))) for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	#entries = np.array(entries)
	#print(entries)

	maxv = max([e[1] for e in entries])
	#print(maxv)

	# Solving
	sol = 0
	seen = set()
	for r in range(2,len(str(maxv))+1):
		i = 1
		while (v := int(str(i)*r)) < maxv:
			i += 1
			if v in seen:
				continue
			for l,h in entries:
				if v >= l and v <= h:
					sol += v
					seen.add(v)
					break

	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

