"""
Solution to Advent of Code 2024 day 16 part 1

Solved using Dijkstra's algorithms, where the state is position and direction, using heapq for the priority queue, and because all distances are increasing we can never find new shorter paths to tiles.
"""
import time
import sys

# tools
import heapq


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	grid = [list(e) for e in entries]
	#print('\n'.join(''.join(e) for e in grid))

	start = [(i,j) for i,row in enumerate(grid) for j,c in enumerate(row) if c == 'S'][0]
	end = [(i,j) for i,row in enumerate(grid) for j,c in enumerate(row) if c == 'E'][0]
	
	# Solving
	costs = {(*start,0,1):0}
	q = [(0,*start,0,1)]
	while q:
		cost, i,j, di,dj = heapq.heappop(q)
		if grid[i][j] == 'E':
			return cost
		if grid[i+di][j+dj] != '#' and (i+di,j+dj, di,dj) not in costs:
			costs[(i+di,j+dj, di,dj)] = cost + 1
			heapq.heappush(q, (cost+1, i+di,j+dj, di,dj))
		if (i,j, int(di==0),int(dj==0)) not in costs:
			costs[(i,j, int(di==0),int(dj==0))] = cost + 1000
			heapq.heappush(q, (cost+1000, i,j, int(di==0),int(dj==0)))
		if (i,j, -int(di==0),-int(dj==0)) not in costs:
			costs[(i,j, -int(di==0),-int(dj==0))] = cost + 1000
			heapq.heappush(q, (cost+1000, i,j, -int(di==0),-int(dj==0)))
	return -1
		

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

