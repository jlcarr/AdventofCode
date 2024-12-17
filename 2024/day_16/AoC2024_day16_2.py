"""
Solution to Advent of Code 2024 day 16 part 2

Solved using same start as Part 1, but also keep track of for each tile and direction the other tiles and directions that could proceed it under optimality. From here we just perform a search backwards from the final position (considering only optimal directions) and keeping track of unique tiles visited on the search backwards. I tried NetworkX but it stalled, likely due to too many possible optimal paths.
"""
import time
import sys

# tools
import heapq
from collections import deque
import networkx as nx


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
	prevs = {(*start,0,1):set()}
	while q:
		cost, i,j, di,dj = heapq.heappop(q)
		#if grid[i][j] == 'E':
		#	return cost
		# forward
		if grid[i+di][j+dj] != '#':
			if (i+di,j+dj, di,dj) not in costs:
				costs[(i+di,j+dj, di,dj)] = cost + 1
				heapq.heappush(q, (cost+1, i+di,j+dj, di,dj))
				prevs[(i+di,j+dj, di,dj)] = set()
			if cost + 1 == costs[(i+di,j+dj, di,dj)]:
				prevs[(i+di,j+dj, di,dj)].add((i,j, di,dj))
		# turn
		if (i,j, int(di==0),int(dj==0)) not in costs:
			costs[(i,j, int(di==0),int(dj==0))] = cost + 1000
			heapq.heappush(q, (cost+1000, i,j, int(di==0),int(dj==0)))
			prevs[(i,j, int(di==0),int(dj==0))] = set()
		if cost + 1000 == costs[(i,j, int(di==0),int(dj==0))]:
			prevs[(i,j, int(di==0),int(dj==0))].add((i,j, di,dj))
		if (i,j, -int(di==0),-int(dj==0)) not in costs:
			costs[(i,j, -int(di==0),-int(dj==0))] = cost + 1000
			heapq.heappush(q, (cost+1000, i,j, -int(di==0),-int(dj==0)))
			prevs[(i,j, -int(di==0),-int(dj==0))] = set()
		if cost + 1000 == costs[(i,j, -int(di==0),-int(dj==0))]:
			prevs[(i,j, -int(di==0),-int(dj==0))].add((i,j, di,dj))
	minc = min(costs[(*end, di,dj)] for di,dj in [(1,0), (-1,0), (0,1), (0,-1)])
	# reverse search
	q = deque()
	for di,dj in [(1,0), (-1,0), (0,1), (0,-1)]:
		if minc == costs[(*end, di,dj)]:
			print(costs[(*end, di,dj)])
			q.append((*end, di,dj))
	pos = set()
	#print(q)
	while q:
		#print(q)
		i,j, di,dj = q.pop()
		pos.add((i,j))
		for p in prevs[(i,j, di,dj)]:
			q.appendleft(p)
	return len(pos)
		
		
	# Network X
	G = nx.Graph()
	for i,row in enumerate(grid):
		for j,c in enumerate(row):
			if c != '#':
				for di,dj in [(1,0), (-1,0), (0,1), (0,-1)]:
					if grid[i+di][j+dj] != '#':
						G.add_edge((i,j,di,dj), (i+di,j+dj,di,dj), cost=1)
					G.add_edge((i,j,di,dj), (i,j, int(di==0),int(dj==0)), cost=1000)
					G.add_edge((i,j,di,dj), (i,j, -int(di==0),-int(dj==0)), cost=1000)
	#return nx.shortest_path_length(G, source=(*start,0,1), target=(*end,1,0), weight='cost')
	visited = set()
	for di,dj in [(1,0), (-1,0), (0,1), (0,-1)]:
		paths = nx.all_shortest_paths(G, source=(*start,0,1), target=(*end,1,0), weight='cost')
		for path in paths:
			for i,j, di,dj in path:
				visited.add((i,j))
	return len(visited)
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

