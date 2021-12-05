"""
Solution to Advent of Code 2021 day 5 part 1

Solved by actually constructing the grid and using numpy's indexing to update it.
There is probably a nicer solution using some tricks on computational geometry.
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
	entries = [re.findall(r'(\d+),(\d+) -> (\d+),(\d+)',e)[0] for e in entries]
	entries = [[int(i) for i in e] for e in entries]
	entries = [e for e in entries if e[0]==e[2] or e[1]==e[3]]
	#print(entries)
	
	maximum_x =  max([i for e in entries for i in e]) +1
	#print(maximum_x)
	arr = np.zeros((maximum_x,maximum_x))

	for i,e in enumerate(entries):
		if e[0]> e[2]:
			e[0],e[2] = e[2],e[0]
		if e[1]>e[3]:
			e[1],e[3] = e[3],e[1]
		if e[0]==e[2]:
			arr[e[0], e[1]:e[3]+1] += 1
		if e[1]==e[3]:
			arr[e[0]:e[2]+1, e[1]] += 1
		#print(e,arr)
	arr = arr.T
	#print(arr)
	sol= np.sum(arr>1)

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

