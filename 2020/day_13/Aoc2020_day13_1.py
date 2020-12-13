"""
Solution to Advent of Code 2020 day 12 part 1

Modular arithmetic
"""
import time
import sys

import re
import math

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	s,deps = entries.splitlines()
	s = int(s)
	deps = [int(x) for x in deps.split(',') if x != 'x']
	#print(deps,s)
	v = [x-1-(s-1)%x for x in deps]
	#print(v)
	m = min(v)
	i = v.index(m)
	#print(m,i,deps[i])
	return deps[i]*m
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
