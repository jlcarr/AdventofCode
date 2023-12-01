"""
Solution to Advent of Code 2023 day 1 part 2

Solved by constructing the list of digits written out, and building up the line string, checking if they end with a digit or digit string.
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

mapping = ['zero','one', 'two','three', 'four', 'five','six','seven','eight','nine']

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	decoded = []
	for e in entries:
		nums = []
		acc = ''
		for c in e:
			acc += c
			if c in '0123456789':
				nums.append(c)
			else:
				for numeral in mapping:
					if acc.endswith(numeral):
						nums.append(mapping.index(numeral))
		decoded.append(nums)
	entries = decoded
	#print(entries)
	entries = [int(str(e[0])+str(e[-1])) for e in entries]
	#print(entries)
	return sum(entries)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

