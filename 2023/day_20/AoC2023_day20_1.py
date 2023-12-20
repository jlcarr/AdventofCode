"""
Solution to Advent of Code 2023 day 20 part 1

Simply perform the simulation by creating mappings of child parent relations, and flip-flop states and conjunction inputs, using a queue for the pulses, keeping track of value, destination and origin.
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
	
	highs = 0
	lows = 0
	for push in range(1000):
		pulses = deque([('broadcaster', 0, '')])
		while pulses:
			module, pulse, mfrom = pulses.pop()
			if pulse == 1:
				highs += 1
			else:
				lows += 1
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
			
	#print(highs, lows)
	return highs * lows


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

