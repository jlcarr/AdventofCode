"""
Solution to Advent of Code 2023 day 8 part 2

First found the cycles and their leads, noticing we need to keep track of which step in the instructions we're on as part of the state. Afterwards notice that target nodes only show up once per cycle and never in the leads. This means solving a system of congruences, with the Chinese Remainder Theorem, since they were all coprime up to the length of the instructionset: the input was generated for this convenience. For some reason Sympy's conguence solver didn't work, but the CRT did the trick.
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

from sympy.ntheory.modular import crt
from sympy.ntheory.modular import solve_congruence
from sympy import primefactors

import math

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	inst, entries = entries.split('\n\n')
	entries = entries.splitlines()
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
	cyclez = {k:[i+1 for i,c in enumerate(v) if c[0].endswith('Z')] for k,v in cycles.items()}
	
	#print(leadz)
	#print(cyclez)
	#print('leadz', [len(v) for v in leadz.values()])
	#print('cyclez', [len(v) for v in cyclez.values()])
	
	#print({k:len(v) for k,v in leads.items()})
	#print({k:len(v) for k,v in cycles.items()})
	
	mod = [len(cycles[s]) for s in starts]
	res = [(len(cycles[s]) + cyclez[s][0]-len(leads[s])+1) % len(cycles[s]) for s in starts]
	
	simple_sol = math.lcm(*mod)
	#print(simple_sol)
	
	#print([primefactors(m) for m in mod])
	
	d = math.gcd(*mod)
	mod = [m//d for m in mod]
	res = [r%m for r,m in zip(res,mod)]
	
	#print(res)
	#print(mod)
	
	#print(list(zip(res, mod)))
	sols = crt(mod, res)
	sols = [s*d for s in sols]
	#sol = solve_congruence(*list(zip(res, mod)))
	#print(sols)
	#for s in sols:
	#	print('sol', s)
	#	for start in starts:
	#		print((s - len(leads[start]) + 1) % len(cycles[start]))
	#		print(cyclez[start])

	sol = next(s for s in sols
		if all(
				(s - len(leads[start]) + 1) % len(cycles[start]) == cyclez[start][-1] % len(cycles[start])
				and s != 0
				for start in starts
		)
	)
	
	return sol



if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

