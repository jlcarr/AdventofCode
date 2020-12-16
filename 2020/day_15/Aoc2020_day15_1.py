"""
Solution to Advent of Code 2020 day 15 part 1

Brute force
"""
import time
import sys

import re

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.split(',')
	entries = [int(e) for e in entries]
	#print(entries)
	
	ages = dict()
	for i,e in enumerate(entries[:-1]):
		ages[e] = i+1
	last = entries[-1]
	for turn in range(len(entries)+1,2020+1):
		if last in ages:
			a = turn-1 - ages[last]
		else:
			a = 0
		#print(turn,a, last, ages)
		ages[last] = turn-1
		last = a
	return a


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
