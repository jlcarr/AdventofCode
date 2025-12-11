"""
Solution to Advent of Code 2025 day 11 part 2

Solved similarly to part 1, but keeping track of target destinations, and just summing the 2 ordering cases.
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
	comps = [e.split(': ')[0] for e in entries]
	outs = [e.split(': ')[1].split(' ') for e in entries]
	#print(comps)
	#print(outs)

	# Solving

	G = {c:ccs for c,ccs in zip(comps,outs)}
	#print(G)

	@cache
	def rec(c, target_stack):
		if not target_stack:
			return 1
		if c == target_stack[0]:
			return rec(c, target_stack[1:])
		if c not in G:
			return 0
		
		return sum(rec(cc, target_stack) for cc in G[c])
			
	return rec('svr',  ('dac', 'fft', 'out')) + rec('svr',  ('fft', 'dac', 'out'))


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

