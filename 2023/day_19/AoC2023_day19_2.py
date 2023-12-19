"""
Solution to Advent of Code 2023 day 19 part 2

Keep track of ranges which are split as each rules is applied to them. When a range is accepted we can easily compute the number of elements within.
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
import math


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	rules,parts = entries.split('\n\n')
	rules = rules.splitlines()
	parts = parts.splitlines()
	parts = [re.findall(r'\{x=(\d+),m=(\d+),a=(\d+),s=(\d+)\}',p)[0] for p in parts]
	parts = [tuple(map(int,p)) for p in parts]

	workflows = dict()
	for r in rules:
		name,r = r.split('{')
		r = r[:-1]
		r = r.split(',')
		r = [re.findall(r'(\w)([\>\<])(\d+):(\w+)',rr)[0] for rr in r[:-1]] + [r[-1]]
		r = [(rr[0], rr[1], int(rr[2]), rr[3]) for rr in r[:-1]] + [r[-1]]
		workflows[name] = r
	workflows['A'] = ['A']
	workflows['R'] = ['R']
	
	#print(workflows)
	#print(parts)
	
	pars = ['x','m','a','s']
	
	sol = 0
	solp = 0
	q = [((1,4000), (1,4000), (1,4000), (1,4000), 'in')]
	while q:
		#print(q, sol, solp)
		(xmin,xmax), (mmin,mmax), (amin,amax), (smin,smax), curr = q.pop()
		mins = {'x': xmin, 'm': mmin, 'a': amin, 's':smin}
		maxs = {'x': xmax, 'm': mmax, 'a': amax, 's':smax}
		
		for step in workflows[curr]:
			if isinstance(step, str):
				if step == 'A':
					sol += math.prod([1+maxs[p]-mins[p] for p in pars])
				elif step == 'R':
					solp += math.prod([1+maxs[p]-mins[p] for p in pars])
					pass
				else:
					q.append((*[(mins[p],maxs[p]) for p in pars], step))
				break
			param,eq,val,state = step
			if eq == '<':
				if mins[param] < val:
					if maxs[param] > val:
						newmaxs = {k:kk for k,kk in maxs.items()}
						newmaxs[param] = val-1
						q.append((*[(mins[p],newmaxs[p]) for p in pars], state))
						mins[param] = val
					else:
						q.append((*[(mins[p],maxs[p]) for p in pars], state))
						break
			elif eq == '>':
				if maxs[param] > val:
					if mins[param] < val:
						newmins = {k:kk for k,kk in mins.items()}
						newmins[param] = val+1
						q.append((*[(newmins[p],maxs[p]) for p in pars], state))
						maxs[param] = val
					else:
						q.append((*[(mins[p],maxs[p]) for p in pars], state))
						break
	#print(sol)
	#print(solp)
	#print(sol+solp)
	#print(4000**4)
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

