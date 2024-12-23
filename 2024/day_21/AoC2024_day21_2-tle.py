"""
Solution to Advent of Code 2024 day 21 part 2

Solved using numpy
More elegant solution
"""
import time
import sys

# tools
import re

import numpy as np
import scipy.ndimage

from collections import Counter
from functools import cache
import heapq


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	#entries = [list(e) for e in entries]
	print(entries)
	
	npad = [
		['7','8','9'],
		['4','5','6'],
		['1','2','3'],
		[' ','0','A'],
	]
	dpad = [
		[' ','^','A'],
		['<','v','>'],
	]
	
	dmap = {
		'^': (-1,0),
		'v': (1,0),
		'<': (0,-1),
		'>': (0,1),
	}

	def moverobot(move, itarget, state):
		i,j = state[itarget]
		if itarget < len(state)-1:
			if move in dmap:
				di,dj = dmap[move]
				if (0 <= i+di < 2) and (0 <= j+dj < 3) and dpad[i+di][j+dj] != ' ':
					newstate = list(state)
					newstate[itarget] = (i+di, j+dj)
					return tuple(newstate)
				else:
					return None
			elif move == 'A':
				return moverobot(dpad[i][j], itarget+1, state)
			else:
				print('INVALID MOVE')
				return None # invalid move?
		else: #numpad
			if move in dmap:
				di,dj = dmap[move]
				if (0 <= i+di < 4) and (0 <= j+dj < 3) and npad[i+di][j+dj] != ' ':
					newstate = list(state)
					newstate[itarget] = (i+di, j+dj)
					return tuple(newstate)
				else:
					return None
			elif move == 'A':
				return npad[i][j]
			else:
				print('INVALID MOVE')
				return None # invalid move?

	# state (r1,r2,r3) = 5 * 5 * 11
	# state r**5,rf = 5**25*11
	nr = 2
	result = 0
	for code in entries:
		state = tuple([(0,2) for _ in range(nr)] + [(3,2)])
		costs = {state: 0}
		prevs = dict()
		q = [(0,state)]
		codecost = 0
		for d in code:
			while q:
				cost, state = heapq.heappop(q)
				#((ir1,jr1), (ir2,jr2), (ir3,jr3)) = state
				#print(d)
				#print(cost, state)
				#print(dpad[ir1][jr1], dpad[ir2][jr2], npad[ir3][jr3])
				#if dpad[ir1][jr1] == 'A' and dpad[ir2][jr2] == 'A' and npad[ir3][jr3] == d
				#	break
				# move
				for k in dmap.keys():
					newstate = moverobot(k, 0, state)
					if newstate is not None and newstate not in costs:
						costs[newstate] = cost + 1
						heapq.heappush(q, (cost + 1, newstate))
						#prevs[newstate] = (state, (k,' ',' '))
				# you enter
				newstate = moverobot('A', 0, state)
				if newstate is not None and newstate not in costs:
					if isinstance(newstate, str):
						if newstate == d: # found!
							codecost = cost+1 # digit cost
							costs = {state: cost+1}
							q = [(cost+1, state)]
							break
					else:
						costs[newstate] = cost + 1
						heapq.heappush(q, (cost + 1, newstate))
						#prevs[newstate] = (state, (k,' ',' '))
			print(d)
		print(codecost)
		result += codecost * int(code[:-1])
	return result

	# wrong 3425656
	#281212077733592

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

