"""
Solution to Advent of Code 2024 day 10 part 1

Solved using iterative stack-based DFS on each of the candidate trailheads and counting up the number of times 9-height positions reached. Funny enough I originally interpreted the problem as the part 2 version (edited out in my posted solution).
"""
import time
import sys

# tools
import numpy as np


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
	
	# Solving, DFS
	result = 0
	for ii in range(m):
		for jj in range(n):
			if grid[ii,jj] == 0:
				#print(ii,jj)
				q = [(ii,jj)]
				searched = set(q)
				while q:
					i,j = q.pop()
					if grid[i,j] == 9:
						result += 1
						continue
					for ip,jp in [(i-1,j),(i+1,j),(i,j-1),(i,j+1)]:
						if (0 <= ip < m) and (0 <= jp < n) and (ip,jp) not in searched and grid[i,j]+1 == grid[ip,jp]:
							q.append((ip,jp))
							searched.add((ip,jp))
	
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

