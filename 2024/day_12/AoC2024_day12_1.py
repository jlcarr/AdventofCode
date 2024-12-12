"""
Solution to Advent of Code 2024 day 12 part 1

Solved using DFS. Make a set of all plot coordinates to search, and find regions with the search and at each step check adjacent for either next plot to search or boundaries, so as to compute the perimeter, as well as the area.
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
	entries = [list(e) for e in entries]
	#print(entries)
	m,n = len(entries),len(entries[0])
	
	# Solving
	unsearched = set([(i,j) for i in range(m) for j in range(n)])
	result = 0
	while unsearched:
		ii,jj = unsearched.pop()
		q = [(ii,jj)]
		currsearched = set(q)
		region = entries[ii][jj]
		area = 0
		perim = 0
		# find the region
		while q:
			i,j = q.pop()
			area += 1
			for ip,jp in [(i+1,j),(i-1,j),(i,j+1),(i,j-1)]:
				if (0 <= ip < m) and (0 <= jp < n) and entries[ip][jp] == region:
					if (ip,jp) not in currsearched:
						currsearched.add((ip,jp))
						q.append((ip,jp))
				else: # if it crosses out of the region, it is an edge
					perim += 1
		unsearched -= currsearched
		#print(region, area, perim)
		result += perim * area
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

