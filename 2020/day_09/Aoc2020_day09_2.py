"""
Solution to Advent of Code 2020 day 9 part 2

Solved by brute force
Don't see how speedups count be made except via paralellism
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = list(map(int,entries))

	target = 556543474

	for i, entry in enumerate(entries):
		s = entry
		j = i+1
		mx = -1
		mn = -1
		while s < target and j < len(entries):
			if mx == -1 or entries[j] > mx:
				mx = entries[j]
			if mn == -1 or entries[j] < mn:
				mn = entries[j]
			s += entries[j]
			j += 1
		if s == target:
			return mx+mn


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
