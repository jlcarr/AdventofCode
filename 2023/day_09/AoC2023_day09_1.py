"""
Solution to Advent of Code 2023 day 9 part 1

Solved by directly doing the repeated difference, keeping track of the last values to sum them. Better solution is to know that this means we have a polynomial, and use an Lagrange polynomial fit.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage
from scipy.interpolate import lagrange

from collections import Counter, deque
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [[int(v) for v in e.split()] for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	#entries = np.array(entries)
	#print(entries)
	
	
	sol = 0
	for e in entries:
		e = np.array(e)
		fins = []
		#print(e != 0)
		while e.size > 0 and np.any(e != 0):
			fins.append(e[-1])
			e = np.diff(e)
		#fins = fins[::-1]
		sol += sum(fins)
	
	return sol
	
	
	sol = 0
	for i,e in enumerate(entries):
		e = np.array(e)
		p = lagrange(np.arange(e.size), e)
		#print(p)
		#print(i, p(e.size), e)
		sol += p(e.size)

	return int(np.round(sol))

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

