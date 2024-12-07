"""
Solution to Advent of Code 2024 day 7 part 1

Solved using itertools to loop over all combinations of operators, and then run through the computation aggregating the result and checking for matches.
"""
import time
import sys

# tools
import itertools


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	left = [int(e.split(': ')[0]) for e in entries]
	right = [list(map(int,e.split(': ')[1].split(' '))) for e in entries]
	#print(left)
	#print(right)
	
	# Solving
	result = 0
	for l,rs in zip(left,right):
		ops_it = itertools.product(['*','+'], repeat=len(rs)-1)
		for ops in ops_it:
			res = rs[0]
			for op,r in zip(ops,rs[1:]):
				if op == '+':
					res += r
				else:
					res *= r
			#print(ops, rs, res, l)
			if res == l:
				result += l
				break
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

