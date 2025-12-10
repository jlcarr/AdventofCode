"""
Solution to Advent of Code 2025 day 10 part 2

Solved by turning the problem from binary to integers and finding the subset which XORs to the target by brute force.
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
from itertools import combinations


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	targets = [re.findall(r'\[(.+)\]',e)[0] for e in entries]
	targets = [tuple(int(c=='#') for c in t) for t in targets]

	buttons = [e.split(' ')[1:-1] for e in entries]
	#print(buttons)
	buttons = [[tuple(map(int,b[1:-1].split(','))) for b in e] for e in buttons]
	#print(targets)
	#print(buttons)

	targets = [sum(tt*2**i for i,tt in enumerate(t)) for t in targets]
	buttons = [[sum(2**i for i in b) for b in bs] for bs in buttons]
	#print(targets)
	#print(buttons)

	#print([len(e) for e in buttons])
	# Solving
	sol = 0
	for i,(t,bs) in enumerate(zip(targets,buttons)):
		#print(t)
		#print(bs)
		done = False
		for r in range(1, len(bs)+1):
			for c in combinations(bs, r):
				agg = 0
				for b in c:
					agg ^= b
				if agg == t:
					sol += r
					done = True
					break
			if done:
				break
		
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

