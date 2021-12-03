"""
Solution to Advent of Code 2021 day 3 part 1

Solved by taking counts and checking if they were the majority.
A more elegant solution would have been with numpy:
entries = np.array([[int(c) for c in row] for row in entries])
counts = entries.sum(axis=0)>=entries.shape[0]/2
int(''.join(counts.astype(int).astype(str)), 2)
"""
import time
import sys

import re
import numpy as np

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	#entries = [int(e) for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	#entries = np.array(entries)
	#print(entries)
	
	# count the occurances of 1s and see if they're the majority
	l = len(entries[0])
	counts = [0]*l
	for i,n in enumerate(entries):
		for j,c in enumerate(n):
			if c=='1':
				counts[j] += 1
	l = len(entries)
	counts = [j>l//2 for j in counts]
	# convert from binary to decimal (and the complement too)
	sol1 =0
	sol2 = 0
	num = 1
	for i,b in enumerate(counts[::-1]):
		if b:
			sol1 += num
		else:
			sol2 += num
		num *= 2
	return sol1*sol2

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

