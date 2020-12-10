"""
Solution to Advent of Code 2020 day 10 part 1

Solved by sorting first, then first different and count.
Brute force
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	
	
	entries = list(map(int,entries))
	entries = sorted(entries)
	entries = [0] + entries + [max(entries)+3]

	#print(entries)
	val = [j-i for i,j in zip(entries[:-1],entries[1:])]
	#print(val)

	return sum([1 for i in val if i==1]) * sum([1 for i in val if i==3])


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
