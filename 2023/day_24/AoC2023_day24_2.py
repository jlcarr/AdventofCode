"""
Solution to Advent of Code 2023 day 24 part 2

Solved by throwing the large system of non-linear integer equations into z3. Had to remove the time variables with algebra, so we only had 6 variables in the end for each initial position and velocity components. Without z3 could have constructed a Lagrangian with the sum of squares of each equation and solved numerically.
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

import z3

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
	
	solver = z3.Solver()
	
	px,py,pz = z3.Int('px'), z3.Int('py'), z3.Int('pz')
	vx,vy,vz = z3.Int('vx'), z3.Int('vy'), z3.Int('vz')
	
	for i in range(n):
		(px1,py1,pz1),(vx1,vy1,vz1) = entries[i]
		solver.add((px - px1) * (vy1 - vy) == (py - py1) * (vx1 - vx))
		solver.add((px - px1) * (vz1 - vz) == (pz - pz1) * (vx1 - vx))
		
	#print(solver.check())
	#print(type(solver.unsat_core()))
	#print()
	if solver.check() == z3.sat:
		model = solver.model()
		#print('x,y,z = ', model.eval(px),model.eval(py),model.eval(pz))
		return model.eval(px+py+pz)
	
	return None


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

