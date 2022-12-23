"""
Solution to Advent of Code 2022 day 21 part 2

This problem was perfect for z3. Simply parse out all the relations, and ensure 'humn' is left as a free variable. One pitfall was to make sure to enforce divisions are only allowed when there aren't remainders.
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
	entries = [e.split(': ') for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	#print(entries)

	# Solving
	
	solver = z3.Solver()
	
	vars = dict()
	for e in entries:
		vars[e[0]] = z3.Int(e[0])
	
	#print(vars)
	
	for e in entries:
		#print(e)
		
		if e[0] == 'humn':
			continue
		
		# const
		if re.match(r"-?\d+", e[1]):
			#print(vars[e[0]] == int(e[1]))
			solver.add(vars[e[0]] == int(e[1]))
			continue
		
		# parse
		expr = e[1].split(' ')

		# root
		if e[0] == 'root':
			#print(vars[expr[0]] == vars[expr[2]])
			solver.add(vars[expr[0]] == vars[expr[2]])
			continue
			
		# other
		if expr[1] == '+':
			#print(vars[e[0]] == vars[expr[0]] + vars[expr[2]])
			solver.add(vars[e[0]] == vars[expr[0]] + vars[expr[2]])
		if expr[1] == '-':
			solver.add(vars[e[0]] == vars[expr[0]] - vars[expr[2]])
		if expr[1] == '*':
			solver.add(vars[e[0]] == vars[expr[0]] * vars[expr[2]])
		if expr[1] == '/':
			solver.add(vars[e[0]] == vars[expr[0]] / vars[expr[2]])
			solver.add(0 == vars[expr[0]] % vars[expr[2]])
			
	#print(solver.check())
	if solver.check() == z3.CheckSatResult(z3.Z3_L_TRUE):
		model = solver.model()
		return model.eval(vars['humn'])
		
	return None

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

