"""
Solution to Advent of Code 2024 day 6 part 2

Solved by iterating over all positions in the grid we could place the obstacle, and then running the simulation on the guard's path, keeping track of previous states to see if we reach a previous state, i.e. a loop, or leave the grid. The state space is size `w*h*d = 67,600`, and so the time complexity is proportional to `w^2*h^2*d = 1,142,440,000`, which is quite large but not quite infeasible. One way to cut down would be to only place the obstacle on positions the guard visits in Part 1, which should cut it down by a factor of 3.
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
	
	# w*h * w*h*d
	#print(grid.shape)
	#print((grid.shape[0] * grid.shape[1])**2 * 4)
	#print((grid.shape[0] * grid.shape[1]) * 4)
	
	istart,jstart = i,j
	result = 0
	for ip in range(grid.shape[0]):
		for jp in range(grid.shape[1]):
			#print(ip,jp)
			if ((ip,jp) == (istart,jstart)) or (grid[ip,jp] == 1):
				continue
			grid[ip,jp] = 1
			# init guard
			i,j = istart,jstart
			d_index = 0
			di,dj = dlist[d_index % len(dlist)]
			# init state track
			visited = set()
			visited.add((i,j,di,dj))
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
					if (i,j,di,dj) in visited:
						result += 1
						break
					visited.add((i,j,di,dj))
			grid[ip,jp] = 0
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

