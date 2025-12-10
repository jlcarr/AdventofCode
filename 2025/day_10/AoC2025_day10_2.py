"""
Solution to Advent of Code 2025 day 10 part 2

Solved using z3, from which it was pretty easy to set up the constraints of the presses summing to respective joltages.
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
from itertools import combinations

import z3

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	#targets = [re.findall(r'\[(.+)\]',e)[0] for e in entries]
	#targets = [tuple(int(c=='#') for c in t) for t in targets]

	buttons = [e.split(' ')[1:-1] for e in entries]
	#print(buttons)
	buttons = [[tuple(map(int,b[1:-1].split(','))) for b in e] for e in buttons]

	targets = [e.split(' ')[-1] for e in entries]
	targets = [tuple(map(int,e[1:-1].split(','))) for e in targets]	

	#print(targets)
	#print(buttons)

	#print([len(e) for e in buttons])

	# Solving
	sol = 0
	for i,(t,bs) in enumerate(zip(targets,buttons)):
		#print(t)
		#print(bs)
		solver = z3.Optimize()

		presses = [z3.Int(f"p_{i}") for i in range(len(bs))]
		solver.minimize(sum(presses))

		# nonegative presses
		for p in presses:
			solver.add(p >= 0)

		# for each target map to buttons
		target_buttons = [[] for i in t]
		for p,b in zip(presses,bs):
			for tt in b:
				target_buttons[tt].append(p)

		for tt,ps in zip(t,target_buttons):
			solver.add( tt == sum(ps))
		
		if solver.check() == z3.sat:
			model = solver.model()
			sol += model.eval(sum(presses)).as_long()

	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

