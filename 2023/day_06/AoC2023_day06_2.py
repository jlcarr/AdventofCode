"""
Solution to Advent of Code 2023 day 6 part 2

I solved it by filtering the spaces and letting the same code as part 1 run for a little longer. The instant solution is `math.ceil(math.sqrt(t**2 - 4*d))`.
"""
import time
import sys

# tools
import math


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = ''.join(c for c in entries if c != ' ')
	ts,ds = entries.splitlines()
	t = int(ts.split(':')[1])
	d = int(ds.split(':')[1])

	# Solving
	#print(ts,ds)
	sol = 0

	for i in range(t):
		myd = i * (t-i)
		if myd > d:
			sol += 1
			
	#print(sol)
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

