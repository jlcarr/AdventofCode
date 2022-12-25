"""
Solution to Advent of Code 2022 day 25 part 1

An exotic base system, easy enough do the interpretation into a number in memory, however as for how to get back, I just threw z3 at it since I knew it would solve it without fuss. Each digit is a variable with bounds.
There's definitely a more elegant and faster way to simply just do the conversion with divisions and looking ahead, but I can't be bothered.
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

import math

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	#print(entries)
	
	def dec(n):
		result = 0
		for i in n:
			if i in '012':
				dig = int(i)
			elif i == '-':
				dig = -1
			elif i == '=':
				dig = -2
			result *= 5
			result += dig
		return result
		
	sym_map = {0: '0', 1: '1', 2: '2', -1: '-', -2: '='}
		
	dec_entries = [dec(e) for e in entries]
	#print(dec_entries)
	
	sum_entries = sum(dec_entries)
			
	s = z3.Solver()
	
	l = 2 + int(math.log(sum_entries)/math.log(5))
	
	expr = 0
	digs = []
	rad = 1
	for i in range(l):
		digs.append(z3.Int(f'dig{i}'))
		s.add(-2 <= digs[i], digs[i] <=2 )
		expr += digs[i] * rad
		rad *= 5
	s.add(sum_entries == expr)

	if s.check() == z3.sat:
		model = s.model()
		sol = [model.eval(digs[i]).as_long() for i in range(l)]
		while sol[-1] == 0 and len(sol) > 1:
			sol.pop()
		
		return ''.join([sym_map[i] for i in sol[::-1]])

	return 0

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

