"""
Solution to Advent of Code 2022 day 22 part 2

After sketching the net on a piece of paper I realized we could use my same approach as part 1 if we also mark some of the empty tiles to "mirror/bounce" the orientation to go around corners. It ended up working very elegantly.
I considered using 3d vectors and vector math and rotations to keep track of orientation and movement, but this ended up being much easier.
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
	entries = entries[:-2]
	#print([list(e) for e in entries])
	m, n = len(entries), max([len(e) for e in entries])
	entries = [list(e)+[' ']*(n-len(e)) for e in entries]
	entries = np.array(entries)
	
	#print(entries)
	
	s = 50
	mirror_map = {
		(0,3): 'bl-tr',
		(1,0): 'tl-br',
		(1,2): 'tl-br',
		(2,3): 'bl-tr',
		(3,1): 'tl-br',
	}
	# test input
	test = False
	if test:
		s = 4
		mirror_map = {
			(0,1): 'tl-br',
			(1,3): 'bl-tr',
			(2,1): 'bl-tr',
			(3,0): 'bl-tr',
			(3,2): 'tl-br',
		}
	
	entries = np.vstack((entries, np.array([[' ']*n]*s)))
	m += s
	entries = np.hstack((entries, np.array([[' ']*s]*m)))
	n += s
	#for row in entries:
	#	print(''.join(row))
	
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
	
	orient_change = {
		'tl-br': {
			(0,1): (1,0),
			(0,-1): (-1,0),
			(1,0): (0,1),
			(-1,0): (0,-1),
		},
		'bl-tr': {
			(0,1): (-1,0),
			(0,-1): (1,0),
			(1,0): (0,-1),
			(-1,0): (0,1),
		}
	}
	
	
	# Solving
	pos = start
	for i,inst in enumerate(insts):
		#print('inst', inst)
		if inst in ['R', 'L']:
			orient = turn[inst][orient]
			continue
		inst = int(inst)
		for j in range(inst):
			new_pos = ((pos[0]-orient[0]+m)%m, (pos[1]+orient[1]+n)%n)
			new_orient = orient
			#print(new_pos)
			while entries[new_pos] == ' ':
				tile = (new_pos[0]//s, new_pos[1]//s)
				if tile in mirror_map:
					if mirror_map[tile] == 'tl-br' and new_pos[0]%s == new_pos[1]%s:
						new_orient = orient_change['tl-br'][new_orient]
						#print('tl-br change', 'tile', tile, 'pos',(new_pos[0]%s,new_pos[1]%s), 'orient', new_orient)
					elif mirror_map[tile] == 'bl-tr' and new_pos[0]%s + new_pos[1]%s == s-1:
						new_orient = orient_change['bl-tr'][new_orient]
						#print('bl-tr change', 'tile', tile, 'pos',(new_pos[0]%s,new_pos[1]%s), 'orient', new_orient)
				new_pos = ((new_pos[0]-new_orient[0]+m)%m, (new_pos[1]+new_orient[1]+n)%n)
			if entries[new_pos] == '#':
				break
			#if entries[new_pos] == '.':
			pos = new_pos
			orient = new_orient
			#print(j, pos)
		#print(pos, orient)

		#entries[pos] = 'A'
		#print(entries)
		#for row in entries:
		#	print(''.join(row))
		#entries[pos] = '.'
	
	#print(((pos[0]+1, pos[1]+1), orient, turn_val[orient]))
	return 1000 * (pos[0]+1) + 4 * (pos[1]+1) + turn_val[orient]

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

