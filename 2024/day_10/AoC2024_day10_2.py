"""
Solution to Advent of Code 2024 day 10 part 2

Solved similar to part 1, but with recursive DFS / DP with memoization to get the count of paths to each 9-height positions.
"""
import time
import sys

# tools
import numpy as np
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [[int(v) if v != '.' else -1 for v in e] for e in entries]
	grid = np.array(entries)
	#print(grid)
	m,n = grid.shape
	
	# Solving, recursive DFS / DP with memoization
	@cache
	def rec(i,j):
		if grid[i,j] == 9:
			return 1
		result = 0
		for ip,jp in [(i-1,j),(i+1,j),(i,j-1),(i,j+1)]:
			if (0 <= ip < m) and (0 <= jp < n) and grid[i,j]+1 == grid[ip,jp]:
				result += rec(ip,jp)
		return result
	
	result = 0
	for ii in range(m):
		for jj in range(n):
			if grid[ii,jj] == 0:
				#print(ii,jj)
				result += rec(ii,jj)
	
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

