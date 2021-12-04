"""
Solution to Advent of Code 2021 day 4 part `

Used Numpy. Keep track of masks of called numbers. Use axial summations to check for solutions.
"""
import time
import sys

import re
import numpy as np


def check_sol(arr):
	is_sol = (arr.sum(axis=0)==0).any()
	#print("vert", is_sol)
	is_sol = is_sol or (arr.sum(axis=1)==0).any()
	#print("hor", is_sol)
	return is_sol

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.split('\n\n')
	
	nums = list(map(int,entries[0].split(',')))
	entries = entries[1:]
	
	entries = [[list(map(int,row.split())) for row in e.splitlines()] for e in entries]
	entries = [np.array(e) for e in entries]
	masks = [np.ones(e.shape, dtype=bool) for e in entries]
	#print(nums)
	#print(entries)
	#print(masks)
	
	# Brute force loop
	sol_puzz = -1
	sol_num = -1
	for c,n in enumerate(nums):
		#print("round", c, n)
		for i,e in enumerate(entries):
			masks[i] = np.logical_and(masks[i], e!=n)
			is_sol = check_sol(masks[i])
			#print(masks[i], is_sol)
			if is_sol:
				sol_puzz = i
				sol_num = n
				break
		if is_sol:
			break
	#print(sol_puzz, sol_num)
	arr = np.sum(entries[sol_puzz] * masks[sol_puzz].astype(int))
	#print(arr)
	return arr*sol_num

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

