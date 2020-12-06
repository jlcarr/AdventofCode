"""
Solution to Advent of Code 2020 day 6 part 1

Solved by brute force
Use set differences
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.split('\n\n')
	entries = [len(set(list(e)) - {'\n'}) for e in entries]
	return sum(entries)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
