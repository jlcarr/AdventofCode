"""
Solution to Advent of Code 2023 day 4 part 2

Similar to part 2, but kept track of the number of compies of each ticket, and performed the addition forward for each win, summing total at the end.
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
	entries = [e.split(': ')[1] for e in entries]
	entries = [[[int(num) for num in side.split(' ') if num] for side in e.split('|')] for e in entries]
	#print(entries)
	counts = [1]*len(entries)
	for i,e in enumerate(entries):
		inters = len(set(e[0]).intersection(set(e[1])))
		for j in range(i+1, i+1+inters):
			counts[j] += counts[i]
	#print(counts)
	return sum(counts)
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

