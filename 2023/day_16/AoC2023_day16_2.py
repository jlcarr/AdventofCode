"""
Solution to Advent of Code 2023 day 16 part 2

Same as part 1, just brute-forced over each possible starting position.
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


mapping = {
	'/': {(0,1): (-1,0), (0,-1): (1,0), (1,0): (0,-1), (-1,0): (0,1)},
	'\\': {(0,1): (1,0), (0,-1): (-1,0), (1,0): (0,1), (-1,0): (0,-1)},
}

def compute(beams, rows, cols, entries):
	searched = set()
	energized = set()

	while beams:
		(px,py),(dx,dy) = beams.pop()
		#print((px,py), (dx,dy), beams)
		if not ((0 <= py < rows) and (0 <= px < cols)):
			continue
		energized.add((px,py))
		if entries[py][px] in mapping:
			dy,dx = mapping[entries[py][px]][(dy,dx)]
			anew = ((px+dx, py+dy), (dx,dy))
			if anew not in searched:
				searched.add(anew)
				beams.append(anew)
		elif entries[py][px] == '|' and dx != 0:
			anew = ((px, py-1), (0,-1))
			if anew not in searched:
				searched.add(anew)
				beams.append(anew)
			anew = ((px, py+1), (0,1))
			if anew not in searched:
				searched.add(anew)
				beams.append(anew)
		elif entries[py][px] == '-' and dy != 0:
			anew = ((px-1, py), (-1,0))
			if anew not in searched:
				searched.add(anew)
				beams.append(anew)
			anew = ((px+1, py), (1,0))
			if anew not in searched:
				searched.add(anew)
				beams.append(anew)
		else:
			anew = ((px+dx, py+dy), (dx,dy))
			if anew not in searched:
				searched.add(anew)
				beams.append(anew)
		
	return len(energized)



def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#for e in entries:
	#	print(e)

	rows,cols = len(entries),len(entries[0])

	result = 0

	for r in range(rows):
		#print('rows', r)
		beams = [((0,r), (1,0))]
		subsol = compute(beams, rows, cols, entries)
		result = max(result, subsol)
		
		beams = [((cols-1,r), (-1,0))]
		subsol = compute(beams, rows, cols, entries)
		result = max(result, subsol)
	
	for c in range(cols):
		#print('cols', c)
		beams = [((c,0), (0,1))]
		subsol = compute(beams, rows, cols, entries)
		result = max(result, subsol)
		
		beams = [((c,rows-1), (0,-1))]
		subsol = compute(beams, rows, cols, entries)
		result = max(result, subsol)
	
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

