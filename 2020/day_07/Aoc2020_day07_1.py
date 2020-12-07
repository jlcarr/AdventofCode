"""
Solution to Advent of Code 2020 day 7 part 1

Solved by set building set up until fixed point
"""
import time
import sys

import re


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = [re.match(r'([\w\s]+) bags contain (.*)\.', entry).groups() for entry in entries]
	#print(entries)
	prev = {}
	valids = {}
	while True:
		valids = set([parent for parent, child in entries if 'shiny gold' in child or any(c in child for c in valids)])
		if len(valids) == len(prev):
			return len(valids)
		prev = valids

	#print(valids)
	return len(valids)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
