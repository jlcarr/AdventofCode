"""
Solution to Advent of Code 2024 day 1 part 2

Solved with similar parsing to part 1, Counter for the counts, and list comprehension with sum to finish off.
"""

import time
import sys

# tools
import numpy as np

from collections import Counter


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [e.split() for e in entries]
	#print(entries)
	entries = [tuple(map(int,e))for e in entries]
	entries = np.array(entries)
	entries = np.sort(entries,axis=0)
	#print(entries)
	
	counts = Counter(entries[:,1])
	sol = sum([i * counts[i] for i in entries[:,0]])
	return sol
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

