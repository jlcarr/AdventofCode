"""
Solution to Advent of Code 2022 day 1 part 2

Solved using part 1 for the simulation, then looking for a cycle where the position in the jet pattern is the same, and the last block dropped is the same and the filled positions are the same. That way we can find the rounds of the cycle remaining and the height difference from each cycle and simply multiply through instead of simulating, finishing off with the remainder heigh difference. I used the last positions of the complete set of blocks as the resting position hash, which worked for this puzzle input.
More proper/general solution would have been to run a flood-fill search on the entire area below the last block for the hash key.
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

import math

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
	#print(len(entries))

	# Solving
	
	# map (it%shapes, lr, turn%entries) -> height
	final_pos = []
	final_map = dict()
	prev_lrs = deque([])
	q_len = len(shapes)
	
	max_width = 7
	filled = set()
	max_height = 0
	turn = 0
	fin = 1000000000000
	it = 0
	
	while it < fin:
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
			#print(turn, turn % len(entries), entries[turn % len(entries)])
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
				# pattern
				final_pos.append(max_height)
				prev_lrs.appendleft(lr)
				while len(prev_lrs) > q_len:
					prev_lrs.pop()
				
				key = (it%len(shapes), tuple(prev_lrs), turn%len(entries))
				if key in final_map:
					cycle = it - final_map[key]
					skip_cycles = (fin - it) // cycle
					leftover = (fin - it) % cycle
					# full cycle
					max_height += skip_cycles * (max_height - final_pos[final_map[key]])
					max_height += final_pos[final_map[key]+leftover] - final_pos[final_map[key]]
					return max_height-1
				elif len(prev_lrs) == q_len:
					final_map[key] = it
				break
				
			#print('\tround', lr, height, entries[it % len(entries)])
		#print('end', lr, height)
		#print(filled)
		it += 1
	return max_height

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

