"""
Solution to Advent of Code 2021 day 6 part 1

Solved by simply simulating the fish reproduction.
More elegant solution is the one to solve pt2 using memoization.
Closed form solution might actually be possible by diagonalizing the state transition matrix.
"""
import time
import sys

import re
import numpy as np

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.split(',')
	entries = [int(e) for e in entries]
	#print(entries)

	for day in range(80):
		l = len(entries)
		for fish in range(l):
			entries[fish] -= 1
			if entries[fish] == -1:
				entries[fish] = 6
				entries.append(8)

	return len(entries)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

