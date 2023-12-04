"""
Solution to Advent of Code 2023 day 4 part 1

Solved using set intersection, and power of 2. Parsing done with splitting.
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
	
	intersects = [set(e[0]).intersection(set(e[1])) for e in entries]
	#print(intersects)
	points = [2**(len(i)-1) for i in intersects if i]
	#print(points)
	return sum(points)
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

