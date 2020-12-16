"""
Solution to Advent of Code 2020 day 2 part 1

Solved by brute force
"""
import time
import sys

import re

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = [re.match(r'(\d+)-(\d+) (\w): (\w+)',entry).groups() for entry in entries]
	# Brute force loop
	valid = [p for l,u,c,p in entries if int(l) <= p.count(c) <= int(u)]
	return len(valid)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
