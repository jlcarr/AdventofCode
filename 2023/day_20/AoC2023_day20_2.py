"""
Solution to Advent of Code 2023 day 20 part 2

In general since we have flip-flops with feedback, it's undecidable if a given circuit would even terminate running, let alone compute the number of presses: ie the problem is incomputable in general. However by assuming the input is crafted to terminate quickly, the number of possible states is 2 to the power of the flip-flops, which therefore must cycle eventually (again using the "always terminates" assumption). However by graphing the input with GraphViz we see 4 disjoint structures all feeding into the final rx, each with a tractable number of states: we can just find the cycle length for those, and then find the LCM, which works.
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
	typemap = dict()
	childmap = dict()
	parentmap = dict()
	entries = entries.splitlines()
	for e in entries:
		module, children = e.split(' -> ')
		mtype = ''
		if module[0] in '%&':
			mtype = module[0]
			module = module[1:]
		children = children.split(', ')
		typemap[module] = mtype
		childmap[module] = children
		for child in children:
			if child not in parentmap:
				parentmap[child] = []
			parentmap[child].append(module)

	#print(typemap)
	#print(childmap)
	#print(parentmap)
	
	ff_states = dict()
	conj_in = dict()
	for k,v in typemap.items():
		if v == '%':
			ff_states[k] = 0
		if v == '&':
			conj_in[k] = {kk:0 for kk in parentmap[k]}
	#print(ff_states)
	#print(conj_in)
	
	
	# GraphViz
	#with open('input.dot', 'w') as f:
	#	f.write('digraph {\n')
	#	for p,cs in childmap.items():
	#		f.write(f'{p} [label="{typemap[p]}{p}"];\n')
	#		for c in cs:
	#			f.write(f'{p} -> {c};\n')
	#	f.write('}')
	# dot -Tpng input.dot > input.png
	
	counterset = ['rx']
	counterset = [p for v in counterset for p in parentmap[v]]
	counterset = [p for v in counterset for p in parentmap[v]]
	#print(counterset)
	countermap = {v:None for v in counterset}
	
	rx = False
	result = 0
	while any(v is None for v in countermap.values()):
		result += 1
		pulses = deque([('broadcaster', 0, '')])
		while pulses:
			module, pulse, mfrom = pulses.pop()
			if module == 'rx' and pulse == 0:
				rx = True
				break
			if mfrom in countermap and countermap[mfrom] is None and pulse == 1:
				countermap[mfrom] = result
				#print(result)
			if module == 'broadcaster':
				for child in childmap[module]:
					pulses.appendleft((child, pulse, module))
			if module not in typemap:
				continue
			if typemap[module] == '%' and pulse == 0:
				ff_states[module] = 1 - ff_states[module]
				for child in childmap[module]:
					pulses.appendleft((child, ff_states[module], module))
			if typemap[module] == '&':
				conj_in[module][mfrom] = pulse
				newpulse = 1 - int(all(v == 1 for v in conj_in[module].values()))
				for child in childmap[module]:
					pulses.appendleft((child, newpulse, module))
	#print(countermap)
	return math.lcm(*list(countermap.values()))
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

