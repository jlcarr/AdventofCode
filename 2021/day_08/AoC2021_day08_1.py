"""
Solution to Advent of Code 2021 day 8 part 1

Solved by simply comparing lengths.
Don't think there's really a simpler solution for this one
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
	entries = [[[sorted(dig) for dig in side.split()] for side in e.split(' | ')] for e in entries]
	#print(entries)

	sol = 0
	for i,e in enumerate(entries):
		sol+= len([dig for dig in e[1] if len(dig) in [2, 4, 3,7]])

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

