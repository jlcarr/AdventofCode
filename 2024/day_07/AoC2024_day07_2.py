"""
Solution to Advent of Code 2024 day 7 part 2

Solved the same way as Part 1, just the extra operation makes it take longer. The concat operation was implemented using string casting.
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
		ops_it = itertools.product(['*','+', '||'], repeat=len(rs)-1)
		for ops in ops_it:
			res = rs[0]
			for op,r in zip(ops,rs[1:]):
				if op == '+':
					res += r
				elif op == '*':
					res *= r
				else:
					res = int(str(res)+str(r))
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

