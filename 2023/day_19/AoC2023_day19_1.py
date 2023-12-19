"""
Solution to Advent of Code 2023 day 19 part 1

Solved by simply implementing the instructions, using a dict for the workflows.
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
	#entries = [re.findall(r'(\w+)\{\w[\>\<]\}',e)[0] for e in entries]
	workflows = dict()
	for r in rules:
		name,r = r.split('{')
		r = r[:-1]
		r = r.split(',')
		r = [re.findall(r'(\w)([\>\<])(\d+):(\w+)',rr)[0] for rr in r[:-1]] + [r[-1]]
		r = [(rr[0], rr[1], int(rr[2]), rr[3]) for rr in r[:-1]] + [r[-1]]
		workflows[name] = r
	
	#print(workflows)
	#print(parts)
	
	sol = 0
	for x,m,a,s in parts:
		part = {'x': x, 'm':m, 'a':a, 's':s}
		curr = 'in'
		while True:
			instr = None
			for step in workflows[curr]:
				if isinstance(step, str):
					instr = step
					break
				#print(step)
				param,eq,val,state = step
				if eq == '<':
					if part[param] < val:
						instr = state
						break
				elif eq == '>':
					if part[param] > val:
						instr = state
						break
			if instr == 'A':
				sol += x+m+a+s
				break
			if instr == 'R':
				break
			curr = instr
	
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

