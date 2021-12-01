"""
Solution to Advent of Code 2021 day 1 part 1

Solved with simple iteration keeping track of the previous value
A smore elegant solution might be to use numpy operations
np.sum(np.diff(entries)>0)
"""
import time
import sys

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	entries = list(map(int,entries))
	
	# Brute force loop
	prev = entries[0]
	count = 0
	for i,n in enumerate(entries[1:]):
		if n >prev:
			count += 1
		prev = n
	return count

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

