"""
Solution to Advent of Code 2020 day 3 part 1

Solved by brute force, gives linear time in height
"""
import time
import sys

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = [list(entry) for entry in entries]
	#print(entries)

	# Brute force loop
	count = 0
	i = 0
	j = 0
	while i < len(entries):
		if entries[i][j] == '#':
			count+=1
		i +=1
		j += 3
		j %= len(entries[0])
	return count

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
