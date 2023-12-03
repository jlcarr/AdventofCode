"""
Solution to Advent of Code 2023 day 2 part 1

Solved by parsing using split, then used a mapping of maximum values and ensured every entry remained under.
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

mapping = {
	'red': 12,
	'green': 13,
	'blue': 14
}

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	#entries = [int(e) for e in entries]
	ids = [int(re.findall(r'Game (\d+):', e)[0]) for e in entries]
	#print(ids)
	entries = [[v2.split(' ') for v in e.split(': ')[1].split('; ') for v2 in v.split(', ')] for e in entries]
	entries = [[(int(v[0]), v[1]) for v in e] for e in entries]
	result = 0
	for i,e in enumerate(entries):
		if all(c <= mapping[col] for c, col in e):
			result += ids[i]
	#print(entries)
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

