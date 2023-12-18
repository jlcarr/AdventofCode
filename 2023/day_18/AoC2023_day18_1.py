"""
Solution to Advent of Code 2023 day 18 part 1

Made of a set of all dug points from the instructions, then bound the bounds and applied flood-fill on the boundary to find the complement area, and compute the final area.
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
	'U': (-1,0),
	'D': (1,0),
	'L': (0,-1),
	'R': (0,1),
}

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [e.split(' ') for e in entries]
	entries = [(e[0],int(e[1]),e[2]) for e in entries]
	#print(entries)
	
	x,y = 0,0
	dug = set()
	dug.add((y,x))
	for d,v,c in entries:
		dy,dx = mapping[d]
		for step in range(v):
			x += dx
			y += dy
			dug.add((y,x))
	
	miny, maxy = min([yx[0] for yx in dug]), max([yx[0] for yx in dug])
	minx, maxx = min([yx[1] for yx in dug]), max([yx[1] for yx in dug])
	#print(miny, maxy, minx, maxx)
	
	founds = set()
	
	# left
	x = minx
	for y in range(miny, maxy+1):
		if (y,x) not in dug and (y,x) not in founds:
			q = [(y,x)]
			while q:
				curry,currx = q.pop()
				for py,px in [(curry-1,currx),(curry+1,currx),(curry,currx-1),(curry,currx+1)]:
					if (miny <= py <= maxy) and (minx <= px <= maxx) \
						and (py,px) not in dug \
						and (py,px) not in founds:
						founds.add((py,px))
						q.append((py,px))
	# right
	x = maxx
	for y in range(miny, maxy+1):
		if (y,x) not in dug and (y,x) not in founds:
			q = [(y,x)]
			while q:
				curry,currx = q.pop()
				for py,px in [(curry-1,currx),(curry+1,currx),(curry,currx-1),(curry,currx+1)]:
					if (miny <= py <= maxy) and (minx <= px <= maxx) \
						and (py,px) not in dug \
						and (py,px) not in founds:
						founds.add((py,px))
						q.append((py,px))
	# up
	y = miny
	for x in range(minx, maxx+1):
		if (y,x) not in dug and (y,x) not in founds:
			q = [(y,x)]
			while q:
				curry,currx = q.pop()
				for py,px in [(curry-1,currx),(curry+1,currx),(curry,currx-1),(curry,currx+1)]:
					if (miny <= py <= maxy) and (minx <= px <= maxx) \
						and (py,px) not in dug \
						and (py,px) not in founds:
						founds.add((py,px))
						q.append((py,px))
	# down
	y = maxy
	for x in range(minx, maxx+1):
		if (y,x) not in dug and (y,x) not in founds:
			q = [(y,x)]
			while q:
				curry,currx = q.pop()
				for py,px in [(curry-1,currx),(curry+1,currx),(curry,currx-1),(curry,currx+1)]:
					if (miny <= py <= maxy) and (minx <= px <= maxx) \
						and (py,px) not in dug \
						and (py,px) not in founds:
						founds.add((py,px))
						q.append((py,px))
	
	return (1+maxy-miny)*(1+maxx-minx) - len(founds)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

