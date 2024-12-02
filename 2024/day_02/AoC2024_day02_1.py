"""
Solution to Advent of Code 2024 day 2 part 1

Solved using Numpy on each row to diff it, and check each difference was within the bounds. We can also check if all differences are positive or negative to check if it's purely ascending or descending.
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
	entries = [[int(c) for c in e.split()] for e in entries]
	
	# Solution
	sol = 0
	for e in entries:
		d  = np.diff(e)
		if (np.all(d < 0) or np.all(d > 0)) and np.all(1 <= np.abs(d)) and np.all(np.abs(d) <= 3):
			sol += 1
	return sol
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

