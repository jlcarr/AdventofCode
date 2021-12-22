"""
Solution to Advent of Code 2021 day 22 part 1

Solved using set operations to keep track of all the on-cubes, with xyz nested loops.
Might have been faster but more memory intensize to create an actual 3D grid.
"""
import time
import sys

import re
import numpy as np

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	#for e in entries:
	#	print(re.findall(r'(on|off) x=(-?\d+)..(-?\d+),y=(-?\d+)..(-?\d+),z=(-?\d+)..(-?\d+)',e))
	entries = [re.findall(r'(on|off) x=(-?\d+)..(-?\d+),y=(-?\d+)..(-?\d+),z=(-?\d+)..(-?\d+)',e)[0] for e in entries]
	entries = [[e[0]]+[int(j) for j in e[1:]] for e in entries]
	#print(entries)

	sol = 0
	cubes_on = set()
	for instruc in entries:
		on_off = instruc[0]
		instruc = instruc[1:]
		if min(instruc) < -50 or max(instruc) > 50:
			continue
		for x in range(instruc[0],instruc[1]+1):
			for y in range(instruc[2],instruc[3]+1):
				for z in range(instruc[4],instruc[5]+1):
					if on_off=='on':
						cubes_on.add((x,y,z))
					elif (x,y,z) in cubes_on:
						cubes_on.remove((x,y,z))

	return len(cubes_on)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

