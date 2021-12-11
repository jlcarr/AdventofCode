"""
Solution to Advent of Code 2021 day 10 part 1

Solved using a stack to store opening brackets.
"""
import time
import sys

import re
import numpy as np

point_map = {
	')': 3,
	']': 57,
	'}': 1197,
	'>': 25137
}

opening_map = {
	')': '(',
	']': '[',
	'}': '{',
	'>': '<'
}


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	#print(entries)

	sol = 0
	for i,n in enumerate(entries):
		stack = []
		for c in n:
			#print(sol, c, stack)
			if c in '([{<':
				stack.append(c)
			if c in opening_map:
				if not stack or stack[-1] != opening_map[c]:
					#print(c)
					sol += point_map[c]
					break
				stack.pop()
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

