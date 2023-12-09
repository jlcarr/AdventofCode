"""
Solution to Advent of Code 2023 day 8 part 2

After finding the cycles and leads, then the system of congruences into z3. Funny enough the optimize doesn't seem to work, but the solver returns the solution almost instantly.
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
	inst, entries = entries.split('\n\n')
	entries = entries.splitlines()
	#entries = [int(e) for e in entries]
	entries = [re.findall(r'(\w+) = \((\w+), (\w+)\)',e)[0] for e in entries]
	G = dict()
	for s,l,r in entries:
		G[s] = (l,r)
	#print(G)
	#print(inst)

	starts = [k for k in G.keys() if k.endswith('A')]
	#print(starts)
	
	# find leads and cycles for each
	leads = dict()
	cycles = dict()
	for start in starts:
		found = set()
		lead = []
		curr = start
		step = 0
		# find cycle
		while (curr, step % len(inst)) not in found:
			found.add((curr, step % len(inst)))
			lead.append((curr, step % len(inst)))
			# update
			if inst[step % len(inst)] == 'L':
				curr = G[curr][0]
			else:
				curr = G[curr][1]
			step += 1
		cycle = []
		while lead[-1] != (curr, step % len(inst)):
			cycle.append(lead.pop())
		cycle.append(lead.pop())
		cycle = cycle[::-1]
		leads[start] = lead
		cycles[start] = cycle
	
	#print('leads', leads)
	#print('cycles', cycles)
		
	leadz = {k:[i for i,c in enumerate(v) if c[0].endswith('Z')] for k,v in leads.items()}
	cyclez = {k:[i for i,c in enumerate(v) if c[0].endswith('Z')] for k,v in cycles.items()}
	
	#print(leadz)
	#print(cyclez)
	#print('leadz', [len(v) for v in leadz.values()])
	#print('cyclez', [len(v) for v in cyclez.values()])
	
	#print({k:len(v) for k,v in leads.items()})
	#print({k:len(v) for k,v in cycles.items()})
	
	
	#solver = z3.Optimize()
	solver = z3.Solver()
	
	z3_steps = z3.Int("steps")
	solver.add(z3_steps >= 0)
	
	z3_vars = []
	for start in starts:
		lead_expr = z3.Or(*[il == z3_steps for il in leadz[start]])
		cycle_expr = z3.Or(*[
			z3.And(
				z3_steps % len(cycles[start]) == (len(leads[start]) + ic) % len(cycles[start]),
				z3_steps >= len(cycles[start])
			)
			for ic in cyclez[start]])
		solver.add(z3.Or(lead_expr, cycle_expr))
	
	#solver.minimize(z3_steps)
			
	#print(solver.check())
	#print(type(solver.unsat_core()))
	
	if solver.check() == z3.sat:
		model = solver.model()
		sol = model.eval(z3_steps)
		return sol
	
	return


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

