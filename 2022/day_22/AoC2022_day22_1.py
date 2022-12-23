"""
Solution to Advent of Code 2022 day 22 part 1

Keep track of the orientation, and have a map for changing the orientation. Walking off edges can be handled with modular arithmetic and not counting steps on empty spots, evaluating the actual step forward lazily in case of a wall.
Perhaps would be more elegant if actual vector arithmetic was use for turning.
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
	#entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	insts = entries[-1]
	insts = re.findall(r'(\d+|L|R)', insts)
	entries = entries[:-1]
	#print([list(e) for e in entries])
	m, n = len(entries), max([len(e) for e in entries])
	entries = [list(e)+[' ']*(n-len(e)) for e in entries]
	entries = np.array(entries)
	#print(entries)
	#print(insts)

	# get start
	start = None
	i = 0
	while start is None:
		j = 0
		while j < n and start is None:
			if entries[i,j] == '.':
				start = (i,j)
			j += 1
		i += 1
	#print(start)
	#entries[start] = 'A'
	#print(entries)
	
	orient = (0,1)
	turn = {
		'L': {
			(0,1): (1,0),
			(1,0): (0,-1),
			(0,-1): (-1,0),
			(-1,0): (0,1),
		},
		'R': {
			(0,1): (-1,0),
			(-1,0): (0,-1),
			(0,-1): (1,0),
			(1,0): (0,1),
		},
	}
	turn_val = {
		(0,1): 0,
		(1,0): 3,
		(0,-1): 2,
		(-1,0): 1,
	}
	
	# Solving
	pos = start
	for i,inst in enumerate(insts):
		#print('inst', n)
		if inst in ['R', 'L']:
			orient = turn[inst][orient]
			continue
		inst = int(inst)
		for j in range(inst):
			new_pos = ((pos[0]-orient[0]+m)%m, (pos[1]+orient[1]+n)%n)
			#print(new_pos)
			while entries[new_pos] == ' ':
				new_pos = ((new_pos[0]-orient[0]+m)%m, (new_pos[1]+orient[1]+n)%n)
			if entries[new_pos] == '#':
				break
			#if entries[new_pos] == '.':
			pos = new_pos
			#print(j, pos)
		#print(pos, orient)

		#entries[pos] = 'A'
		#print(entries)
		#for row in entries:
		#	print(''.join(row))
		#entries[pos] = '.'
		
	return 1000 * (pos[0]+1) + 4 * (pos[1]+1) + turn_val[orient]

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

