"""
Solution to Advent of Code 2021 day 14 part 2

Solved by keeping track of pair frequency counts.
A fair bit of code could probably have been saved by using Python's defaultdict
"""
import time
import sys

import re
import numpy as np
import copy

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	polymer,instructions = entries.split('\n\n')
	poly_map = [e.split(' -> ') for e in instructions.splitlines()]
	poly_map = {e[0]:e[1] for e in poly_map}
	#print(poly_map)
	#print(polymer)

	# Initial counts
	pair_list = {}
	for j in range(len(polymer)-1):
		pair = polymer[j]+polymer[j+1]
		if pair not in pair_list:
			pair_list[pair] = 0
		pair_list[pair] += 1

	#print(pair_list)

	# Iterating
	for i in range(40):
		new_pair_list = dict()
		for pair,count in pair_list.items():
			if pair in poly_map:
				new_pair1 = pair[0] + poly_map[pair]
				new_pair2 = poly_map[pair] + pair[1]
				if new_pair1 not in new_pair_list:
					new_pair_list[new_pair1] = 0
				new_pair_list[new_pair1] += count
				if new_pair2 not in new_pair_list:
					new_pair_list[new_pair2] = 0
				new_pair_list[new_pair2] += count
			else:
				if pair not in new_pair_list:
					new_pair_list[pair] = 0
				new_pair_list[pair] += count
		pair_list = new_pair_list
		#break
		#print(pair_list)

	# Count the letter frequencies
	counts = {}
	for pair,count in pair_list.items():
		for c in pair:
			if c not in counts:
				counts[c] = 0
			counts[c] += count
	# Account for the the end letter not being counted twice
	counts[polymer[0]] += 1
	counts[polymer[-1]] += 1
	# Account for every letter being counted twice
	counts = {c:count//2 for c,count in counts.items()}
	#print(counts)
	return max(counts.values()) - min(counts.values())


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

