"""
Solution to Advent of Code 2025 day 9 part 2

Solved using Shapely to contruct the main polygon and then check containment over all pairs of points for the rectangles.
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


def makepoly(ps):
	return unary_union([
		geometry.Polygon([(x+i/2, y+j/2) for x,y in ps])  
		for i in range(-1,1+1) 
		for j in range(-1,1+1)
	]).normalize().simplify(0.1)

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [tuple(map(int,e.split(','))) for e in entries]
	#entries = np.array(entries)
	#print(entries)

	# Solving
	main_poly = makepoly(entries)

	sol = 0
	l = len(entries)
	for i,e in enumerate(entries):
		#print(i)
		x1,y1 = e
		for j in range(i+1,l):
			x2,y2 = entries[j]
			ps = [(x1,y1), (x2,y1), (x2,y2), (x1,y2)]
			poly = makepoly(ps)
			if main_poly.contains(poly):
				sol = max(sol, poly.area)
		
	return int(round(sol))


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

