"""
Solution to Advent of Code 2021 day 6 part 2

Solved using dynamic programming with memoization.
Closed form solution might actually be possible by diagonalizing the state transition matrix.
"""
import time
import sys

import re
import numpy as np

memo = -np.ones((9,256+1), dtype=int)

def fish_produced(timer, days_remaining):
	#print(timer, days_remaining)
	if memo[timer, days_remaining] == -1:
		if days_remaining == 0:
			memo[timer, days_remaining] = 1
		elif timer > 0:
			memo[timer, days_remaining] = fish_produced(timer-1, days_remaining-1)
		else:
			memo[timer, days_remaining] = fish_produced(6, days_remaining-1) + fish_produced(8, days_remaining-1)
	return memo[timer, days_remaining]

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.split(',')
	entries = [int(e) for e in entries]
	#print(entries)

	sol = sum([fish_produced(t, 256) for t in entries])

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

