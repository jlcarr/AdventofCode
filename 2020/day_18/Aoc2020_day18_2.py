"""
Solution to Advent of Code 2020 day 18 part 2

Same as day 1
"""
import time
import sys

import numpy as np
from scipy import ndimage

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = [list(e) for e in entries]

	return int(np.sum(entries))

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
