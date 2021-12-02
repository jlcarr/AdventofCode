"""
Solution to Advent of Code 2021 day 2 part 1

Solved by simple iteration keeping track of the previous values
I don't think there's a more elegant solution.
"""
import time
import sys

import numpy as np

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	entries = [(e.split(' ')[0],int(e.split(' ')[1])) for e in entries]
	#entries = np.array(entries)
	
	# Brute force loop
	f = 0
	d = 0
	a = 0
	for dir,n in entries:
		if dir[0]=='f':
			f += n
			d += n*a
		if dir[0]=='d':
			a += n
		if dir[0]=='u':
			a -= n
	return d*f

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

