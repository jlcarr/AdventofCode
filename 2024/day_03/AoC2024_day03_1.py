"""
Solution to Advent of Code 2024 day 3 part 1

Solved using regex with capture groups, then a list comprehension it integer casting to finish up.
"""
import time
import sys

# tools
import re


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing and Solution
	entries = re.findall(r'mul\((\d+),(\d+)\)',entries)
	#print(entries)
	return sum([int(e[0])*int(e[1]) for e in entries])


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

