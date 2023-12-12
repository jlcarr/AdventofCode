"""
Solution to Advent of Code 2023 day 12 part 2

Same dynamic programming as part 1, just increasing the input size as directed.
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
	entries = entries.splitlines()
	entries = [e.split(' ') for e in entries]
	entries = [(e[0], list(map(int,e[1].split(',')))) for e in entries]
	#print(entries)


	result = 0
	for t, vs in entries:
		cache = dict()
		vs = vs*5
		t = (t+'?')*5
		t = t[:-1]
		def rec(it,iv,hcount, t,vs,cache):
			#print(it,iv,hcount)
			if iv > len(vs):
				return 0
			if iv == len(vs):
				for iit in range(it, len(t)):
					if t[iit] == '#':
						hcount += 1
				if hcount > 0:
					return 0
				return 1
				
			if it == len(t):
				if hcount > 0:
					if hcount != vs[iv]:
						return 0
					iv += 1
				if iv == len(vs):
					return 1
				return 0
			
			
			if (it,iv,hcount) in cache:
				return cache[(it,iv,hcount)]
			
			if t[it] == '.':
				if hcount > 0:
					if hcount == vs[iv]:
						return rec(it+1,iv+1,0, t,vs,cache)
					return 0
				return rec(it+1,iv,0, t,vs,cache)
			
			if t[it] == '#':
				return rec(it+1,iv,hcount+1, t,vs,cache)
				
			if t[it] == '?':
				# treat as '.'
				subsol = 0
				if hcount > 0:
					if hcount == vs[iv]:
						temp = rec(it+1,iv+1,0, t,vs,cache)
						cache[(it+1,iv+1,0)] = temp
						subsol += temp
				else:
					temp = rec(it+1,iv,0, t,vs,cache)
					cache[(it+1,iv,0)] = temp
					subsol += temp
				
				# treat as '#'
				temp = rec(it+1,iv,hcount+1, t,vs,cache)
				cache[(it+1,iv,hcount+1)] = temp
				subsol += temp
				return subsol
		#print(t,vs)
		#print(t,vs, rec(0,0,0, t,vs,cache))
		#print(cache)
		result += rec(0,0,0, t,vs,cache)
				
	return result
				

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

