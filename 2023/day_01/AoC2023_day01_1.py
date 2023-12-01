"""
Solution to Advent of Code 2023 day 1 part 1

Solved by just filtering the string with list comprehension.
"""
import time
import sys

# tools
import re
import json

from collections import Counter, deque
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [[c for c in e if c in '0123456789'] for e in entries]
	#print(entries)
	entries = [int(e[0]+e[-1]) for e in entries]
	#print(entries)
	return sum(entries)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

