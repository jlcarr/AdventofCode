"""
Solution to Advent of Code 2024 day 8 part 2

Solved similar to Part 1, but after getting the position difference walk starting from one of the nodes as far as possible in each direction marking nodes. I made the position differences in lowest terms via GCD, however this didn't actually make a difference on the input.
"""
import time
import sys

# tools
import numpy as np
import itertools
import math


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
			dd = math.gcd(di,dj)
			di //= dd
			dj //= dd
			# first
			nodei,nodej = i1,j1
			while (0 <= nodei < m) and (0 <= nodej < n):
				nodes[nodei,nodej] = 1
				nodei += di
				nodej += dj
			# second
			nodei,nodej = i1,j1
			while (0 <= nodei < m) and (0 <= nodej < n):
				nodes[nodei,nodej] = 1
				nodei -= di
				nodej -= dj
	#print(nodes)
	return nodes.sum()


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

