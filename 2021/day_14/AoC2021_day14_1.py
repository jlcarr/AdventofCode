"""
Solution to Advent of Code 2021 day 14 part 1

Direct simulation by looping over the string and appending to a new string.
"""
import time
import sys

import re
import numpy as np

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	polymer,instructions = entries.split('\n\n')
	poly_map = [e.split(' -> ') for e in instructions.splitlines()]
	poly_map = {e[0]:e[1] for e in poly_map}
	#print(poly_map)
	#print(polymer)

	# Perform the solution
	for i in range(10):
		new_poly = ""
		for j in range(len(polymer)-1):
			new_poly += polymer[j]
			pair = polymer[j]+polymer[j+1]
			if pair in poly_map:
				new_poly += poly_map[pair]
		new_poly += polymer[-1]
		polymer = new_poly
		#break
	#print(new_poly)

	# Count the letter frequencies
	counts = {}
	for c in polymer:
		if c not in counts:
			counts[c] = 0
		counts[c] += 1

	return max(counts.values()) - min(counts.values())

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

