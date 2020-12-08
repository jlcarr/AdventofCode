"""
Solution to Advent of Code 2020 day 4 part 2

Solved by brute force
Don't see how speedups count be made except via paralellism
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	insset = set()
	i = 0
	acc = 0
	while i not in insset:
		insset.add(i)
		ins, v = entries[i].split(' ')
		#print(i,ins,v,acc)
		if ins == 'jmp':
			i += int(v)
			continue
		elif ins == 'acc':
			acc += int(v)
		i += 1
	return acc
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
