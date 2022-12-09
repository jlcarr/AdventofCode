"""
Solution to Advent of Code 2022 day 9 part 1

Solved creating the map of all moves needed. Also not a move is only needed if the difference in one dimension is greater than 1. Also count coordinates in a set.
More elegant solution would be to come up with the formula for the moves.
"""
import time
import sys

# tools
import re

import numpy as np
import scipy.ndimage

from collections import Counter
from functools import cache


diff_map = {
	(2,0): [1,0],
	(-2,0): [-1,0],
	(0,2): [0,1],
	(0,-2): [0,-1],
	
	(2,1): [1,1],
	(2,-1): [1,-1],
	
	(-2,1): [-1,1],
	(-2,-1): [-1,-1],
	
	(1,2): [1,1],
	(-1,2): [-1,1],
	
	(1,-2): [1,-1],
	(-1,-2): [-1,-1],
}

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [e.split(' ') for e in entries]
	entries = [(e[0],int(e[1])) for e in entries]
	#print(entries)

	# Solving
	h = [0,0]
	t = [0,0]
	pos_set = set([tuple(t)])
	#print(pos_set)
	for i,n in enumerate(entries):
		for j in range(n[1]):
			if n[0] == 'R':
				h[0] += 1
			elif n[0] == 'L':
				h[0] -= 1
			elif n[0] == 'U':
				h[1] += 1
			elif n[0] == 'D':
				h[1] -= 1
			diff = [h[0] - t[0], h[1] - t[1]]
			if not all([abs(p) <= 1 for p in diff]):
				move = diff_map[tuple(diff)]
				t[0] += move[0]
				t[1] += move[1]
			#print(n)
			#print(h,t)
			#print()
			pos_set.add(tuple(t))
			
	#print(pos_set)
	return len(pos_set)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

