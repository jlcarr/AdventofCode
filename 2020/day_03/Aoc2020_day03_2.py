"""
Solution to Advent of Code 2020 day 3 part 2

Solved by brute force
Don't see how speedups count be made except via paralellism
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
	result = 1
	for i_p,j_p in [(1,1),(1,3),(1,5),(1,7),(2,1)]:
		count = 0
		i = 0
		j = 0
		while i < len(entries):
			if entries[i][j] == '#':
				count+=1
			i += i_p
			j += j_p
			j %= len(entries[0])
		result *= count
	return result

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
