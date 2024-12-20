"""
Solution to Advent of Code 2024 day 20 part 1

Solved using a cache of distances from each position, computed via extra simple search, then for each positon check each direction for a possible cheat and if the cheat results in a better time using the difference in cached distances.
"""
import time
import sys

# tools
# None


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	grid = [list(e) for e in entries]
	#print('\n'.join(''.join(e) for e in grid))
	
	# Setup
	m,n = len(grid),len(grid[0])
	start = [(i,j) for i,row in enumerate(grid) for j,c in enumerate(row) if c == 'S'][0]
	end = [(i,j) for i,row in enumerate(grid) for j,c in enumerate(row) if c == 'E'][0]
	
	# Solving
	dists = {start:0}
	curr = start
	while curr != end:
		i,j = curr
		for di,dj in [(1,0), (-1,0), (0,1), (0,-1)]:
			if grid[i+di][j+dj] != '#' and (i+di, j+dj) not in dists:
				dists[(i+di, j+dj)] = dists[(i, j)] + 1
				curr = (i+di, j+dj)
				break
	#print(dists)
	
	cheats = dict()
	for (i,j), cost in dists.items():
		for di,dj in [(2,0), (-2,0), (0,2), (0,-2)]:
			if (0 <= i+di < m) and  (0 <= j+dj < n) and grid[i+di][j+dj] != '#':
				save = dists[(i+di,j+dj)] - dists[(i,j)] - 2
				if save <= 0:
					continue
				if save not in cheats:
					cheats[save] = []
				cheats[save].append((i,j))
	cheatcounts = {i:len(v) for i,v in cheats.items()}
	#print(cheatcounts)
	return sum(v for k,v in cheatcounts.items() if k >= 100)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

