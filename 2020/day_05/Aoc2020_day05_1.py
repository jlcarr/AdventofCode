"""
Solution to Advent of Code 2020 day 5 part 1

Converting from binary.
"""
import time
import sys

import re


def decode_row(s):
	result = 0
	for i,c in enumerate(s[::-1]):
		if c == 'B':
			result += 2**i
	return result


def decode_col(s):
	result = 0
	for i,c in enumerate(s[::-1]):
		if c == 'R':
			result += 2**i
	return result


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	
	# Brute force loop
	valid = [decode_row(p[:7])*8+decode_col(p[-3:]) for p in entries]
	return max(valid)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
