"""
Solution to Advent of Code 2022 day 12 part 1

Same as part one, but searched for all starting points and iterated over them to get the best result. Had to use try/except for NetworkX's NetworkXNoPath error.
More elegant would be to directly use shortest_path_length.
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

import networkx as nx

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	SE = {'S':0, 'E':ord('z')-ord('a')}
	grid = [[ord(j)-ord('a') if j not in SE else SE[j] for j in e] for e in entries]
	grid = np.array(grid)
	m,n = grid.shape
	S_set = []
	for i in range(m):
		for j in range(n):
			if grid[i][j] == 0:
				S_set.append((i,j))
			if entries[i][j] == 'E':
				E = (i,j)
	#print(entries)
	#print(grid)
	#print(S_set, E)

	G = nx.DiGraph()
	for i in range(m):
		for j in range(n):
			if i-1 >= 0 and grid[i-1][j] <= grid[i][j]+1:
				G.add_edge((i,j),(i-1,j))
			if i+1 < m and grid[i+1][j] <= grid[i][j]+1:
				G.add_edge((i,j),(i+1,j))
			if j-1 >= 0 and grid[i][j-1] <= grid[i][j]+1:
				G.add_edge((i,j),(i,j-1))
			if j+1 < n and grid[i][j+1] <= grid[i][j]+1:
				G.add_edge((i,j),(i,j+1))
			
	result = m*n
	for S in S_set:
		try:
			path = nx.dijkstra_path(G, S, E)
			result = min(result, len(path)-1)
		except:
			pass
				
	return result

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

