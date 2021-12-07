"""
Solution to Advent of Code 2021 day 7 part 1

Solved using hill climbing starting from the mean.
Looking online it seems the true solution is just to use the median.
"""
import time
import sys

import re
import numpy as np


def fuel_cost(entries, pos):
	return sum([abs(e-pos) for e in entries])

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.split(',')
	entries = [int(e) for e in entries]
	#print(entries)

	sol = int(sum(entries)/len(entries))
	sol = min(entries)
	curr = sum([abs(e-sol) for e in entries])

	changed = True
	while changed:
		#print(sol, curr)
		changed = False
		# Plus
		new_sol = sol+1
		new_curr = fuel_cost(entries, new_sol)
		#print("+", new_sol, new_curr)
		if new_curr < curr:
			sol = new_sol
			curr = new_curr
			changed = True
			continue
		# Minus
		new_sol = sol-1
		new_curr = fuel_cost(entries, new_sol)
		#print("-", new_sol, new_curr)
		if new_curr < curr:
			sol = new_sol
			curr = new_curr
			changed = True
			continue

	#print(sol, curr)
	return curr

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

