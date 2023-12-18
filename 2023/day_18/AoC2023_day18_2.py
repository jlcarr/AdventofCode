"""
Solution to Advent of Code 2023 day 18 part 2

This time used Shapely to do the geometry computations. Each instruction is a rectangle, so union them all, take the exterior polygon's area.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage

from collections import Counter, deque
from functools import cache

from shapely import geometry
from shapely.ops import polygonize, unary_union

mapping = {
	3: (-1,0),
	1: (1,0),
	2: (0,-1),
	0: (0,1),
}

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [e.split(' ')[-1][2:-1] for e in entries]
	entries = [(int(e[:-1], 16), int(e[-1])) for e in entries]
	
	#x,y = 0,0
	#lines = []
	#line = [(y,x)]
	#for v,d in entries:
	#	dy,dx = mapping[d]
	#	lines.append((y,x, y+dy*v, x+dx*v))
	#	y += dy*v
	#	x += dx*v
	#	line.append((y,x))
		
	x,y = 0,0
	polys = []
	for v,d in entries:
		dy,dx = mapping[d]
		if dy == 0:
			polys.append(geometry.Polygon([(y-0.5,x-dx*0.5), (y+0.5,x-dx*0.5), (y+0.5,x+dx*(v+0.5)), (y-0.5,x+dx*(v+0.5))]))
		if dx == 0:
			polys.append(geometry.Polygon([(y-dy*0.5,x-0.5), (y-dy*0.5,x+0.5), (y+dy*(v+0.5),x+0.5), (y+dy*(v+0.5),x-0.5)]))
		y += dy*v
		x += dx*v
	
	polygon = unary_union(polys)
	exterior = geometry.Polygon(polygon.exterior)
	return int(exterior.area)
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

