"""
Solution to Advent of Code 2020 day 1 part 1

Solved by brute force O(n^2)
Linear time could be made by using a dict to cache past results
"""
import time

def solution():
	with open('input.txt','r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = list(map(int,entries))
	# Brute force loop
	for i,n1 in enumerate(entries[:-1]):
		for n2 in entries[i:]:
			if n1+n2 == 2020:
				return n1*n2

if __name__ == "__main__":
	start = time.time()
	answer = solution()
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
