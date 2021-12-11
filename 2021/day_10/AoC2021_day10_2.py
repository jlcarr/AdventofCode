"""
Solution to Advent of Code 2021 day 10 part 2

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
point_map = {
	'(': 1,
	'[': 2,
	'{': 3,
	'<': 4
}

opening_map = {
	')': '(',
	']': '[',
	'}': '{',
	'>': '<'
}

closing_map = {v:k for k,v in opening_map.items()}


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	#print(entries)

	break_again = False
	sol_list = []
	for i,n in enumerate(entries):
		stack = []
		for c in n:
			#print(sol, c, stack)
			if c in '([{<':
				stack.append(c)
			if c in opening_map:
				if not stack or stack[-1] != opening_map[c]:
					break_again = True
					break
				stack.pop()
		if break_again:
			break_again = False
			continue
		# remaining line
		temp_sol = 0
		while stack:
			c = stack.pop()
			temp_sol *= 5
			temp_sol += point_map[c]
		sol_list.append(temp_sol)
	#print(sol_list)
	sol_list.sort()
	#print(sol_list)
	sol = sol_list[len(sol_list)//2]
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

