"""
Solution to Advent of Code 2023 day 6 part 2

Similar to part 2, just updated the `Counter` logic to be cleaner, and for the wild-cards its always advantageous to match the most common already in hand (avoiding more Js). Realized should added in case of ties to use highest, but funny enough it still worked.
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

mapping = {'T': 10, 'J': 1, 'Q': 12, 'K': 13, 'A': 14}

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	bids = [int(e.split()[1]) for e in entries]
	hands =[[int(c) if c not in mapping else mapping[c] for c in e.split()[0]] for e in entries]
	#print(bids)
	#print(hands)

	types = []
	for h in hands:
		if 1 in h:
			temp = [(v,c) for v,c in Counter(h).most_common() if v != 1]
			if temp:
				h = [v if v != 1 else temp[0][0] for v in h]
		c = Counter(Counter(h).values())
		if c[5] == 1: # 5 kind
			types.append(7)
		elif c[4] == 1: # 4 kind
			types.append(6)
		elif c[3] == 1 and c[2] == 1: # full house
			types.append(5)
		elif c[3] == 1: # 3 kind
			types.append(4)
		elif c[2] == 2: # 2 pair
			types.append(3)
		elif c[2] == 1: # 1 pair
			types.append(2)
		else: # none
			types.append(1)

	index = list(range(1, len(hands)+1))
	vals = list(zip(types, hands, bids, index))
	
	vals = sorted(vals)
	
	#print(vals)
	
	sol = 0
	for r, (t,h, b, i) in enumerate(vals):
		sol += (r+1) * b
		
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

