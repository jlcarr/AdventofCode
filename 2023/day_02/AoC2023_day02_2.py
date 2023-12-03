"""
Solution to Advent of Code 2023 day 2 part 2

Solved parsing with splitting then keeping track of the maximum values of each color seen in each entry.
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
	ids = [int(re.findall(r'Game (\d+):', e)[0]) for e in entries]
	entries = [[[c.split(' ') for c in h.split(', ')] for h in e.split(': ')[1].split('; ')] for e in entries]
	entries = [[[(int(c[0]), c[1]) for c in h] for h in e] for e in entries]
	#print(entries)
	
	result = 0
	for i,e in enumerate(entries):
		mins = {'red': 0,'green': 0,'blue': 0}
		for h in e:
			for c,col in h:
				mins[col] = max(mins[col], c)
		result += mins['red'] * mins['green'] * mins['blue']
	#print(entries)
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

