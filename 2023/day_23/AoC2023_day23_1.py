"""
Solution to Advent of Code 2023 day 23 part 1

The hint about going downhill implies there will be no possible loops. So we can give an id to each branch we are exploring, updated at each junction we reach: we cannot go to a node with the same id, or back onto a predecessor, since that would be backtracking. Otherwise we're just trying to find the longest route possible by updating a mapping of longest distances to get to a given node found so far with a typical graph traversal.
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
import heapq

mapping = {
	'^': (-1,0),
	'v': (1,0),
	'>': (0,1),
	'<': (0,-1),
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
	#print(entries)
	
	rows,cols = len(entries), len(entries[0])
	
	start = (0,1)
	end = (rows-1,cols-2)

	# Solving
	id_levels = [0]
	q = [start]
	ids = {start: 0}
	preds = {start: -1}
	maxid = 0
	dists = {start: 0}
	#pathmap = {start:[start]}
	while q:
		(i,j) = q.pop()
		neighbors = []
		for di,dj in [(-1,0),(1,0),(0,-1),(0,1)]:
			ip,jp = i+di,j+dj
			if not ((0 <= ip < rows) and (0 <= jp < cols)): # inside
				continue
			if entries[ip][jp] == '#': # not wall
				continue
			if entries[i][j] in mapping and mapping[entries[i][j]] != (di,dj): # limit icy
				continue
			if (ip,jp) in ids and ids[(ip,jp)] == ids[(i,j)]: # no backtrack
				continue
			if (ip,jp) in ids and ids[(ip,jp)] == preds[(i,j)]: # no backtrack
				continue
			if (ip,jp) in dists and dists[(ip,jp)] >= dists[(i,j)] + 1:
				continue
			neighbors.append((ip,jp))
		
		for ip,jp in neighbors:
			if (ip,jp) not in dists:
				#pathmap[(ip,jp)] = pathmap[(i,j)] + [(ip,jp)]
				dists[(ip,jp)] = dists[(i,j)] + 1
			#if  dists[(i,j)] + 1 > dists[(ip,jp)]:
				#pathmap[(ip,jp)] = pathmap[(i,j)] + [(ip,jp)]
			dists[(ip,jp)] = max(dists[(ip,jp)], dists[(i,j)] + 1)
			if len(neighbors) > 1:
				#print((i,j))
				maxid += 1
				ids[(ip,jp)] = maxid
				preds[(ip,jp)] = ids[(i,j)]
			else:
				ids[(ip,jp)] = ids[(i,j)]
				preds[(ip,jp)] = preds[(i,j)]
		
			q.append((ip,jp))
		#if max(dists.values()) > 100:
		#	break
	#print(ids)
	#for i in range(rows):
	#	print(''.join(['X' if (i,j) in q else ('O' if (i,j) in dists else entries[i][j]) for j in range(cols)]))
	#print(q)
	#print(rows,cols)
	#for i in range(rows):
	#	print(''.join(['O' if (i,j) in pathmap[end] else entries[i][j] for j in range(cols)]))
	#for i,j in pathmap[end]:
	#	print(i,j,dists[(i,j)])
	#print(np.diff(np.array([dists[(i,j)] for i,j in pathmap[end]])))
	
	return dists[end]


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

