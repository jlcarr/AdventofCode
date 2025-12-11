"""
Solution to Advent of Code 2025 day 11 part 1

Solved using recursion with memoization to traverse the graph DFS counting up the number of paths.
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
	def rec(c):
		if c == 'out':
			return 1
		if c not in G:
			return 0
		
		return sum(rec(cc) for cc in G[c])
			
	return rec('you')


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

