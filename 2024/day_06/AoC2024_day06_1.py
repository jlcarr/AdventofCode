"""
Solution to Advent of Code 2024 day 6 part 1

Solved by simply performing the walk, using a cyclic array of directions, and keeping a copy of the grid to marking visited positions, which is summed for the answer.
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
	entries = [list(e) for e in entries]
	entries = np.array(entries)
	guard = entries == '^'
	i,j = np.argwhere(guard)[0]
	grid = (entries == '#').astype(int)
	#print(grid)
	#print(i,j)
	
	# Solving
	dlist = [(-1,0),(0,1),(1,0),(0,-1)]
	d_index = 0
	di,dj = dlist[d_index % len(dlist)]
	
	visited = np.zeros_like(grid)
	visited[i,j] = 1
	while (0 <= i+di < grid.shape[0]) and (0 <= j+dj < grid.shape[1]):
		#print((i,j),(di,dj))
		i += di
		j += dj
		if grid[i][j] == 1:
			i -= di
			j -= dj
			d_index += 1
			di,dj = dlist[d_index % len(dlist)]
		else:
			visited[i,j] = 1
	#print(visited)
	return visited.sum()


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

