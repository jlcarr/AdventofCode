"""
Solution to Advent of Code 2022 day 1 part 2

Solved by simply simulating the falling, and keeping track of the max height. Filled positions are kept in a set for quick checking for collisions.
Might have been more efficient literally create a numpy array of the board.
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


shapes = """
####

.#.
###
.#.

..#
..#
###

#
#
#
#

##
##
"""
shapes = [[list(row) for row in s.strip().splitlines()] for s in shapes.split('\n\n') if s.strip()]

lr_diff = {'<': -1, '>': 1}

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = list(entries)
	#print(shapes)
	#print(entries)

	# Solving
	max_width = 7
	filled = set()
	max_height = 0
	turn = 0
	for it in range(2022):
		#print('it', it)
		rock = shapes[it % len(shapes)]
		#print(np.array(rock))
		h,w = len(rock), len(rock[0])
		lr = 2
		height = max_height + 3
		#print('start', lr, height)
		while True:
			# blow
			new_lr = lr + lr_diff[ entries[turn % len(entries)] ]
			#print(entries[turn % len(entries)], lr_diff[ entries[turn % len(entries)]])
			# check
			crash = False
			for i in range(h):
				for j in range(w):
					if rock[-i-1][j] == '#' \
						and ((new_lr+j, height+i) in filled or not (0<= new_lr+j <max_width)):
						crash = True
					if crash:
						break
				if crash:
					break
			if not crash:
				lr = new_lr
			turn += 1
			# fall
			new_height = height -1
			# check
			crash = False
			for i in range(h):
				for j in range(w):
					#print('\t', (lr+j, new_height+i))
					if rock[-i-1][j] == '#' \
						and ((lr+j, new_height+i) in filled or not (0<= new_height+j )):
						crash = True
					if crash:
						break
				if crash:
					break
			if not crash:
				height = new_height
			if crash:
				for i in range(h):
					for j in range(w):
						if rock[-i-1][j] == '#':
							#print('\t', (lr+j, height+i))
							filled.add((lr+j, height+i))
							max_height = max(max_height, height+i+1)
				break
			#print('\tround', lr, height, entries[it % len(entries)])
		#print('end', lr, height)
		#print(filled)
	return max_height

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

