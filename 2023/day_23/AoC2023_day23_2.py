"""
Solution to Advent of Code 2023 day 23 part 2

Run through the grid identifying junctions, then search from each junction to find neighboring junctions and the distance to them, thus construct the simplified weighted graph. Use dynamic programming to find the simple path of maximum total distance.
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
	#	print(''.join(e))
	#print(entries)
	
	rows,cols = len(entries), len(entries[0])
	
	start = (0,1)
	end = (rows-1,cols-2)


	# find all junctions, give them indices
	# find distances to neighboring junctions to make weighted graph
	# use dynamic prog to finish

	junctions = set()
	junctions.add(start)
	junctions.add(end)
	for i in range(rows):
		for j in range(cols):
			if entries[i][j] == '#': # not wall
				continue
			neighbors = 0
			for di,dj in [(-1,0),(1,0),(0,-1),(0,1)]:
				ip,jp = i+di,j+dj
				if not ((0 <= ip < rows) and (0 <= jp < cols)): # inside
					continue
				if entries[ip][jp] == '#': # not wall
					continue
				neighbors += 1
			if neighbors > 2:
				junctions.add((i,j))
	
	G = dict()
	for si,sj in junctions:
		G[(si,sj)] = dict()
		q = [(si,sj)]
		dists = {(si,sj):0}
		while q:
			#print(q)
			i,j = q.pop()
			neighbors = []
			for di,dj in [(-1,0),(1,0),(0,-1),(0,1)]:
				ip,jp = i+di,j+dj
				if not ((0 <= ip < rows) and (0 <= jp < cols)): # inside
					continue
				if entries[ip][jp] == '#': # not wall
					continue
				if (ip,jp) in dists:
					continue
				dists[(ip,jp)] = dists[(i,j)] + 1
				if (ip,jp) in junctions:
					G[(si,sj)][(ip,jp)] = dists[(ip,jp)]
				else:
					q.append((ip,jp))
			#if len(dists) > 2:
			#	break
		#break
	
	jnum = {v:i for i,v in enumerate(junctions)}
	#print(junctions)
	#print(G)
	#print(jnum)

	@cache
	def rec(curr, visited):
		#print(curr,visited)
		visited = list(visited)
		if curr == end:
			return 0
		result = -1
		for neighbor,dist in G[curr].items():
			if visited[jnum[neighbor]]:
				continue
			visited[jnum[neighbor]] = True
			subresult = rec(neighbor, tuple(visited))
			if subresult > -1:
				result = max(result, subresult + dist)
			visited[jnum[neighbor]] = False
		return result

	return rec(start, (False,)*len(junctions))


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

