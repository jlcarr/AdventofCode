"""
Solution to Advent of Code 2021 day 1 part 2

Solved by simple iteration keeping track of the previous 3 values
Again numpy could probably lead to a more element solution
np.sum(np.diff(np.convolve(entries, [1,1,1], mode='valid'))>0)
np.sum((entries[3:]-entries[:-3])>0)
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
	prev1 = entries[0]
	prev2 = entries[1]
	prev3 = entries[2]
	count = 0
	for i,n in enumerate(entries[3:]):
		if n + prev3 + prev2 > prev3 + prev2 + prev1:
			count += 1
		prev1 = prev2
		prev2 = prev3
		prev3 = n
	return count

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

