"""
Solution to Advent of Code 2022 day 21 part 1

Simply ran through the process of elimination until the root was found.
Another approach perhaps would have been to use eval and check the available variables, but I couldn't get it to work.
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
	entries = dict([e.split(': ') for e in entries])
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	#print(entries)

	# Solving
	known = dict()
	
	for k in list(entries.keys()):
		if re.match(r"-?\d+", entries[k]):
			known[k] = int(entries[k])
			del entries[k]
	
	while 'root' not in known:
		for k in list(entries.keys()):
			#print(k, entries[k])
			expr = entries[k].split(' ')
			if expr[0] in known and expr[2] in known:
				if expr[1] == '+':
					known[k] = known[expr[0]] + known[expr[2]]
				if expr[1] == '-':
					known[k] = known[expr[0]] - known[expr[2]]
				if expr[1] == '*':
					known[k] = known[expr[0]] * known[expr[2]]
				if expr[1] == '/':
					known[k] = known[expr[0]] // known[expr[2]]
				del entries[k]
		#print(known)
	return known['root']

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

