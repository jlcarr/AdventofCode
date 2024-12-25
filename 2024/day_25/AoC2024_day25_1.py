"""
Solution to Advent of Code 2024 day 25 part 1

Solved using numpy to construct to construct the arrays of the schematics and sum the first row to determine if we have a key or a lock, and sum along the vertical axis to get the heights. Finally just brute force check all pairs of keys and locks by summing their column heights and checking no columns exceed the the size.
"""
import time
import sys

# tools
import numpy as np


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.split('\n\n')
	entries = [(np.array([list(r) for r in e.splitlines()]) == '#').astype(int) for e in entries]
	#for e in entries:
	#	print(e)
		
	# Setup
	keys = [e for e in entries if e[0,:].sum() == 0]
	locks = [e for e in entries if e[0,:].sum() == e.shape[1]]
	#print(len(keys))
	#print(len(locks))
	# 250 * 250
	
	#for k in keys:
	#	print(k)
	#for l in locks:
	#	print(l)
	
	keys = [k.sum(axis=0)-1 for k in keys]
	#print(keys)
	locks = [l.sum(axis=0)-1 for l in locks]
	#print(locks)

	# Solving
	result = 0
	for l in locks:
		for k in keys:
			#print(k,l, k+l)
			if (k+l > l.shape[0]).sum() == 0:
				result += 1
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

