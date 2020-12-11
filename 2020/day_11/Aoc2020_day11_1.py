"""
Solution to Advent of Code 2020 day 11 part 1

Brute force
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = list(map(list,entries))
	#print(entries)

	change = True
	while change:
		#for row in entries:
		#	print(''.join(row))
		#print()
		#print(entries)
		change = False
		nex = [[col for col in row] for row in entries]
		for i,row in enumerate(entries):
			for j,col in enumerate(row):
				count = 0
				if j > 0 and entries[i][j-1] == '#':
					count += 1
				if j < len(row)-1 and entries[i][j+1] == '#':
					count += 1
				if i > 0 and entries[i-1][j] == '#':
					count += 1
				if i < len(entries)-1 and entries[i+1][j] == '#':
					count += 1
				if j > 0 and i < len(entries)-1 and entries[i+1][j-1] == '#':
					count += 1
				if j < len(row)-1 and i > 0 and entries[i-1][j+1] == '#':
					count += 1
				if j > 0 and i > 0 and entries[i-1][j-1] == '#':
					count += 1
				if j < len(row)-1  and i < len(entries)-1 and entries[i+1][j+1] == '#':
					count += 1
				if col == 'L' and count ==0:
					nex[i][j] = '#'
					change = True
				if col == '#' and count >=4:
					nex[i][j] = 'L'
					change = True
		entries = nex
	return sum([1 for row in entries for col in row if col == '#'])
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
