"""
Solution to Advent of Code 2024 day 1 part 1

Solved using split, and numpy for the the array sorting, differencing, absolute valueing and summing.
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
	entries = entries.splitlines()
	entries = [e.split() for e in entries]
	#print(entries)
	entries = [tuple(map(int,e))for e in entries]
	entries = np.array(entries)
	entries = np.sort(entries,axis=0)
	#print(entries)
	#print(entries[:,0]-entries[:,1])
	ans = np.abs(entries[:,0]-entries[:,1])
	#print(ans)
	sol = ans.sum()
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

