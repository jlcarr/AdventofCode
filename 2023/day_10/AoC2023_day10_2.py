"""
Solution to Advent of Code 2023 day 10 part 2

Ended up using the Shapely library to check for polygon containing points. Had to do a traversal around the polygon to get all the points in the correct order. Tried implementing a winding-number solution but it didn't work.
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

from shapely import geometry

mapping = {
	'S': [(0,-1), (0,1), (-1,0), (1,0)],
	'-': [(0,-1), (0,1)],
	'|': [(-1,0), (1,0)],
	'J': [(-1,0), (0,-1)],
	'L': [(-1,0), (0,1)],
	'7': [(1,0), (0,-1)],
	'F': [(1,0), (0,1)],
	'.': [],
}

mapping2 = {
	'J': {(1,0): -1, (0,1): 1},
	'L': {(1,0): 1, (0,-1): -1},
	'7': {(-1,0): 1, (0,1): -1},
	'F': {(-1,0): -1, (0,-1): 1},
}



def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#for e in entries:
	#	print(e)

	w,h = len(entries[0]), len(entries)

	start = None
	for r,e in enumerate(entries):
		for c,v in enumerate(e):
			if v == 'S':
				start = (r,c)
	
	# classify start
	i,j = start
	connex = []
	for ix,jx in mapping[entries[i][j]]:
		if (0 <= i+ix < h) \
			and (0 <= j+jx < w) \
			and (-ix,-jx) in mapping[entries[i+ix][j+jx]]:
			connex.append((ix,jx))
	connex = sorted(connex)
	for k,v in mapping.items():
		if sorted(v) == connex:
			#print('Start = ', k)
			entries[i][j] = k
	
	
	q = deque([start])
	d = {start:0}
	
	while q:
		i,j = q.pop()
		#print('search', (i,j))
		for ix,jx in mapping[entries[i][j]]:
			if (0 <= i+ix < h) \
				and (0 <= j+jx < w) \
				and (-ix,-jx) in mapping[entries[i+ix][j+jx]] \
				and (i+ix, j+jx) not in d:
				#print('find', (i+ix, j+jx), d[(i, j)] + 1)
				q.appendleft((i+ix, j+jx))
				d[(i+ix, j+jx)] = d[(i, j)] + 1
	
	#print(d)
	
	pipes = set()
	ground = set()
	
	rots = dict()
	
	# determine start
	i,j = start
	for ix,jx in mapping[entries[i][j]]:
		if (i+ix, j+jx) in d:
			q.appendleft((i+ix, j+jx))
			if entries[i][j] in mapping2:
				rots[start] = -mapping2[entries[i][j]][(-ix,-jx)]
			break
	
	
	line = [start, q[0]]
	
	searched = {start, q[0]}
	while q:
		i,j = q.pop()
		for ix,jx in mapping[entries[i][j]]:
			if (i+ix, j+jx) in d and (i+ix, j+jx) not in searched:
				searched.add((i+ix, j+jx))
				q.appendleft((i+ix, j+jx))
				if entries[i+ix][j+jx] in mapping2:
					rots[(i+ix,j+jx)] = mapping2[entries[i+ix][j+jx]][(ix,jx)]
				line.append((i,j))
	rsum = sum(rots.values())
	#print(rots)
	#print(rsum)
	
	line = geometry.LineString(line)
	polygon = geometry.Polygon(line)
	#print(polygon)

	sol = 0
	for i in range(h):
		for j in range(w):
			if (i,j) not in d and polygon.contains(geometry.Point(i, j)):
				sol += 1
	return sol
	
	# Not working winding-number solution attempt
	inside = set()
	
	# final
	searched = set()
	for i in range(h):
		for j in range(w):
			if (i,j) not in searched and (i,j) not in d:
				subrot = 0
				escape = False
				q.appendleft((i,j))
				subsearched = set()
				while q:
					print(i,j)
					i,j = q.pop()
					for ix in [-1,0,1]:
						for jx in [-1,0,1]:
							if (0 <= i+ix < h) and (0 <= j+jx < w):
								if (i+ix, j+jx) in rots:
									subrot += rots[(i+ix, j+jx)]
								if (i+ix,j+jx) not in d and (i+ix,j+jx) not in searched:
									q.appendleft((i+ix,j+jx))
									searched.add((i+ix,j+jx))
									subsearched.add((i+ix,j+jx))
							else:
								escape = True
				if not escape and (rsum > 0) == (subrot > 0):
					inside |= subsearched
					
	print(inside)
	
	return len(inside)
				

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

