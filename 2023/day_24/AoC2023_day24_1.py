"""
Solution to Advent of Code 2023 day 24 part 1

Just iterated over all pairs and did the algebra to find the intersections, checking if parallel first. Use algebra as well to make sure the time of the intersecctions is positive. Then just count all intersections that fall in the bounds.
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

#import sympy
# px1,vx1,py1,vx1,t1 = sympy.symbols('px1,vx1,py1,vx1,t1')
# px2,vx2,py2,vx2,t2 = sympy.symbols('px2,vx2,py2,vx2,t2')
# x,y = sympy('x,y')
# x = px1 + vx1 * t1
# x = px2 + vx2 * t2

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [[tuple(map(int,v.split(','))) for v in e.split(' @ ')] for e in entries]
	#print(entries)
	
	n = len(entries)
	
	minv = 200000000000000 #7
	maxv = 400000000000000 #27
	#crossings = []
	result = 0
	for i in range(n):
		(px1,py1,pz1),(vx1,vy1,vz1) = entries[i]
		for j in range(i+1,n):
			(px2,py2,pz2),(vx2,vy2,vz2) = entries[j]
			if vx1 * vy2 == vx2 * vy1: # parallel
				continue
			# y = t * vy1 + py1
			# x = t * vx1 + px1
			# t = (x - px1) / vx1
			# y = (x - px1) * vy1 / vx1 + py1
			# (x - px1) * vy1 / vx1 + py1 = y = (x - px2) * vy2 / vx2 + py2
			# x*vy1*vx2 - px1*vy1*vx2  = x*vy2*vx1 - px2*vy2*vx1 + (py2-py1)*vx1*vx2
			# x*(vy1*vx2 - vy2*vx1)  = px1*vy1*vx2 - px2*vy2*vx1 + (py2-py1)*vx1*vx2
			# x = (px1*vy1*vx2 - px2*vy2*vx1 + (py2-py1)*vx1*vx2)/(vy1*vx2 - vy2*vx1)
			x = (px1*vy1*vx2 - px2*vy2*vx1 + (py2-py1)*vx1*vx2)/(vy1*vx2 - vy2*vx1)
			y = (x - px1) * vy1 / vx1 + py1
			t1 = (x - px1) / vx1
			t2 = (x - px2) / vx2
			if t1 >= 0 and t2 >=0:
				#crossings.append((x,y))
				if (minv <= x <= maxv) and (minv <= y <= maxv):
					result += 1
			#else:
			#print(i,j, ':', (x,y), t1, t2)
	
	#print(crossings)
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

