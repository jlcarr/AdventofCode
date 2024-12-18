"""
Solution to Advent of Code 2024 day 18 part 1

Solved using Dijkstra's algorithm with heapq, only keeping track of coordinates with the inacccessible in a set.
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
	entries = [e.split(',') for e in entries]
	entries = [tuple(map(int,e)) for e in entries]
	#print(entries)
	
	# Solving
	first = 1024 # 12
	bound = 70 #6
	
	fallen = set(entries[:first])
	costs = {(0,0):0}
	q = [(0,0,0)]
	while q:
		cost, i,j = heapq.heappop(q)
		if i == bound and j == bound:
			return cost
		for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]:
			if (0 <= i+di <= bound) and (0 <= j+dj <= bound) and \
				(i+di,j+dj) not in fallen and (i+di,j+dj) not in costs:
				costs[(i+di,j+dj)] = cost + 1
				heapq.heappush(q, (cost+1, i+di,j+dj))
	return -1


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

