"""
Solution to Advent of Code 2024 day 3 part 2

Similar to part 1, but also capturing "do" and "dont't", then using a complete for-loop to keep track of the state when doing the sum.
"""
import time
import sys

# tools
import re


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing & Solution
	entries = re.findall(r'mul\((\d+),(\d+)\)|(do\(\))|(don\'t\(\))',entries)
	#print(entries)
	state = True
	sol = 0
	for l,r,d,dn in entries:
		if d:
			state = True
		elif dn:
			state = False
		elif state:
			sol += int(l)*int(r)
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

