"""
Solution to Advent of Code 2023 day 5 part 1

Solved by parsing up the mappings, then for each seed going through each range to see if any can update the value.
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
	entries = entries.split('\n\n')
	seeds = list(map(int, entries[0].split(': ')[1].split()))
	#print('seeds', seeds)
	
	entries = [e.splitlines()[1:] for e in entries[1:]]
	entries = [[list(map(int, rng.split())) for rng in e] for e in entries]
	#print(entries)

	for i,e in enumerate(entries):
		newseeds = []
		for s in seeds:
			newseeds.append(s)
			for rng in e:
				if rng[1] <= s < rng[1]+rng[2]:
					newseeds[-1] = (s-rng[1]) + rng[0]
					break
		seeds = newseeds
		#print(i,seeds)
	#print(seeds)
	return min(seeds)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

