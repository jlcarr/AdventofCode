"""
Solution to Advent of Code 2024 day 12 part 2

Solved using Shapely. We can perform the DFS on each region as in Part 1, then we can construct the squares for each plot as polygons, union them into the region, simplify the geometry to remove collinear edges, and then Shapely gives us the exterior and interior polygons for free: counting up the number of vertices, which is also the number of sides, finishes off the problem.
"""
import time
import sys

# tools
from shapely import geometry
from shapely.ops import polygonize, unary_union


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#entries = np.array(entries)
	#print(entries)
	m,n = len(entries),len(entries[0])
	
	unsearched = set([(i,j) for i in range(m) for j in range(n)])
	result = 0
	while unsearched:
		ii,jj = unsearched.pop()
		q = [(ii,jj)]
		currsearched = set(q)
		region = entries[ii][jj]
		area = 0
		perim = 0
		polys = []
		sides = 0
		while q:
			i,j = q.pop()
			area += 1
			polys.append(geometry.Polygon([(i,j), (i+1,j), (i+1,j+1), (i,j+1)]))
			for ip,jp in [(i+1,j),(i-1,j),(i,j+1),(i,j-1)]:
				if (0 <= ip < m) and (0 <= jp < n) and entries[ip][jp] == region:
					if (ip,jp) not in currsearched:
						currsearched.add((ip,jp))
						q.append((ip,jp))
				else:
					perim += 1
		
		# join all the plots together into a region, normalize and simplify removes collinear edges
		polygon = unary_union(polys).normalize().simplify(0.1)
		
		exterior = polygon.exterior
		sides = len(exterior.coords.xy[0])-1
		#print(sides)
		for interior in polygon.interiors:
			#print(interior)
			sides += len(interior.coords.xy[0])-1
		unsearched -= currsearched
		#print(region, area, perim, sides, sides * area, exterior, polys)
		result += sides * area
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

