"""
Solution to Advent of Code 2024 day 19 part 2

Solved the same way as part 1, but storing the count of ways to get to each position in the target towel.
"""
import time
import sys

# tools
import re

import numpy as np
import scipy.ndimage

from collections import Counter
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	base,targets = entries.split('\n\n')
	base = base.split(', ')
	targets = targets.splitlines()
	#print(base)
	#print(targets)
	
	# Setup
	trie = dict()
	for w in base:
		curr = trie
		for c in w:
			if c not in curr:
				curr[c] = dict()
			curr = curr[c]
		curr['END'] = None
	#print(trie)
	
	# Solving
	result = 0
	for w in targets:
		reachable = [0] * (len(w)+1) # have covered all before
		reachable[0] = 1
		for i in range(len(w)):
			if not reachable[i]:
				continue
			curr = trie
			j = i
			while j < len(w) and w[j] in curr:
				curr = curr[w[j]]
				j += 1
				if 'END' in curr:
					reachable[j] += reachable[i]
		#print(w, reachable)
		result += int(reachable[-1])
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

