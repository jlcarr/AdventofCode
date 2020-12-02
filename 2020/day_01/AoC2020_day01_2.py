"""
Solution to Advent of Code 2020 day 1 part 2

Solved by brute force O(n^3)
"""
import time
import sys

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = list(map(int,entries))
	# Brute force loop
	for i,n1 in enumerate(entries[:-2]):
		for j,n2 in enumerate(entries[i:-1]):
			for n3 in entries[i+j:]:
				if n1+n2+n3 == 2020:
					return n1*n2*n3

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
