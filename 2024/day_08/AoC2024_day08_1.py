"""
Solution to Advent of Code 2024 day 8 part 1

Solved using itertools to go over every pair of positions for each antenna, which I'd stored in a dictionary. On each pair take the difference in positions and use that to offset again from each, and tally up all the unique positions.
"""
import time
import sys

# tools
import numpy as np
import itertools


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	grid = [list(e) for e in entries]
	#print(np.array(grid))
	
	# Setup
	m,n = len(grid),len(grid[0])
	nodes = np.zeros((m,n),dtype=int)
	#print(nodes)
	# fill antenae
	antenae = dict()
	for i in range(m):
		for j in range(n):
			if grid[i][j] == '.':
				continue
			if grid[i][j] not in antenae:
				antenae[grid[i][j]] = []
			antenae[grid[i][j]].append((i,j))
	
	# Solving
	#print(nodes)
	for k,ps in antenae.items():
		#print(k)
		for (i1,j1),(i2,j2) in itertools.combinations(ps,2):
			#print((i1,j1),(i2,j2))
			di,dj = i2-i1, j2-j1
			# first
			nodei,nodej = i2+di,j2+dj
			if (0 <= nodei < m) and (0 <= nodej < n):
				nodes[nodei,nodej] = 1
			# second
			nodei,nodej = i1-di,j1-dj
			if (0 <= nodei < m) and (0 <= nodej < n):
				nodes[nodei,nodej] = 1
	#print(nodes)
	return nodes.sum()
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

