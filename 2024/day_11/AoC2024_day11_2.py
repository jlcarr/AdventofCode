"""
Solution to Advent of Code 2024 day 11 part 2

Solved using Counter to keep track of the counts of each number, since the order doesn't actually matter, and then create a new Counter with the updates in the numbers.
"""
import time
import sys

# tools
from collections import Counter


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.split(' ')
	entries = [int(e) for e in entries]
	entries = Counter(entries)
	#print(entries)

	# Solving
	for i in range(75):
		new = Counter()
		for k,c in entries.items():
			if k == 0:
				new[1] += c
			elif len(str(k)) % 2 == 0:
				v = str(k)
				new[int(v[:len(v)//2])] += c
				new[int(v[len(v)//2:])] += c
			else:
				new[k*2024] += c
		entries = new
		#break
	#print(entries)
	return sum(c for c in entries.values())


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

