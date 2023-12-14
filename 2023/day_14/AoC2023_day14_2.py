"""
Solution to Advent of Code 2023 day 14 part 2

The solution is to find the cycle, and compute the number of the remaining and subtract them out, so we only have the remainder of the cycle left. Used a hash on the ordered tuple of all rock positions to quick lookups.
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
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#for e in entries:
	#	print(e)
		
	#print('Update')
	rows,cols = len(entries), len(entries[0])
	
	cycles = 1000000000
	
	state_to_index = dict()
	
	done = False
	cycle = 0
	while cycle < cycles:
		cycle += 1
		#print('cycle', cycle)
		for step in range(4):
			#print('step', step, cycle)
			p = step % 4
			if p == 0: # north none
				pass
			elif p == 1: # west transpose
				entries = list(map(list, zip(*entries)))
			elif p == 2: # south v-flip clip
				entries = entries[::-1]
			elif p == 3: # east v-flip + transpose
				entries = list(map(list, zip(*entries)))
				entries = entries[::-1]
			
			for c in range(cols):
				rlag = deque([])
				for r in range(rows):
					if entries[r][c] == 'O' and rlag:
						entries[rlag.pop()][c] = 'O'
						entries[r][c] = '.'
						rlag.appendleft(r)
					elif entries[r][c] == '.':
						rlag.appendleft(r)
					elif  entries[r][c] == '#':
						rlag = deque([])
						
			if p == 0: # north none
				pass
			elif p == 1: # west transpose
				entries = list(map(list, zip(*entries)))
			elif p == 2: # south v-flip clip
				entries = entries[::-1]
			elif p == 3: # east v-flip + transpose
				entries = entries[::-1]
				entries = list(map(list, zip(*entries)))
			
			#for e in entries:
			#	print(e)
		# hash
		hashdata = []
		for r in range(rows):
			for c in range(cols):
				if entries[r][c] == 'O':
					hashdata.append(r)
					hashdata.append(c)
		hashvalue = hash(tuple(hashdata))
		
		if not done and hashvalue in state_to_index:
			cycle_start = state_to_index[hashvalue]
			cycle_len = cycle - cycle_start
			cycles_rem = (cycles - cycle) // cycle_len
			cycle = cycle + cycles_rem * cycle_len
		else:
			state_to_index[hashvalue] = cycle
		
	sol = 0
	for r in range(rows):
		for c in range(cols):
			if entries[r][c] == 'O':
				sol += rows - r
				
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

