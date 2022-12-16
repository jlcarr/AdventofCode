"""
Solution to Advent of Code 2022 day 1 part 2

The elegant solution
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

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [re.findall(r'Sensor at x=(-?\d+), y=(-?\d+): closest beacon is at x=(-?\d+), y=(-?\d+)',e)[0] for e in entries]
	entries = [tuple([int(i) for i in e]) for e in entries]
	#print(entries)

	freq = 4000000
	bound = 4000000
	#bound = 20

	# Solving
	solver = z3.Solver()
	def z3_abs(x):
		return z3.If(x >= 0, x, -x)
	x = z3.Int("x")
	y = z3.Int("y")
	
	solver.add(0 <= x, x <= bound)
	solver.add(0 <= y, y <= bound)
	
	for i,n in enumerate(entries):
		d = abs(n[0]-n[2]) + abs(n[1]-n[3])
		solver.add(z3_abs(x-n[0]) + z3_abs(y-n[1]) > d)
		
	#print(type(solver.check()))
	if solver.check() == z3.CheckSatResult(z3.Z3_L_TRUE):
		model = solver.model()
		return model.eval(freq * x + y)
	return None

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

