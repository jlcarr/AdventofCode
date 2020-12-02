"""
Solution to Advent of Code 2020 day 2 part 1

Solved by brute force
Don't see how speedups count be made except via paralellism
"""
import time

import re

def solution():
	with open('input.txt','r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = [re.match(r'(\d+)-(\d+) (\w): (\w+)',entry).groups() for entry in entries]
	# Brute force loop
	valid = [p for l,u,c,p in entries if int(l) <= p.count(c) <= int(u)]
	return len(valid)

if __name__ == "__main__":
	start = time.time()
	answer = solution()
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
