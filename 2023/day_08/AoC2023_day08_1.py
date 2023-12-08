"""
Solution to Advent of Code 2023 day 8 part 1

We simply perform the simulation until the destination is reached.
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
	inst, entries = entries.split('\n\n')
	entries = entries.splitlines()
	entries = [re.findall(r'(\w+) = \((\w+), (\w+)\)',e)[0] for e in entries]
	G = dict()
	for s,l,r in entries:
		G[s] = (l,r)
	#print(G)
	#print(inst)

	steps = 0
	curr = 'AAA'
	while curr != 'ZZZ':
		for i in inst:
			if i == 'L':
				curr = G[curr][0]
			else:
				curr = G[curr][1]
			steps += 1
			if curr == 'ZZZ':
				break

	return steps


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

