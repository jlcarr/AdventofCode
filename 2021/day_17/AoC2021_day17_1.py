"""
Solution to Advent of Code 2021 day 17 part 2

Brute force searched all reasonable starting values for the max.
More elegant solution using math.
"""
import time
import sys

import re
import numpy as np

def simulate(v, bounds):
	pos = [0,0]
	max_y = 0
	while pos[0] <= bounds[1] and pos[1] >= bounds[2]:
		#print(pos, v)
		pos[0] += v[0]
		pos[1] += v[1]
		v[0] -= np.sign(v[0], dtype=int)
		v[1] -= 1
		if pos[1] > max_y:
			max_y = pos[1]
		#print(bounds[0] <= pos[0] <= bounds[1], bounds[2] <= pos[1] <= bounds[3])
		if bounds[0] <= pos[0] <= bounds[1] and bounds[2] <= pos[1] <= bounds[3]:
			return max_y
	return -1

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = re.match(r'target area: x=(-?\d+)..(-?\d+), y=(-?\d+)..(-?\d+)', entries).groups()
	entries = [int(e) for e in entries]
	x_min,x_max,y_min,y_max = entries
	#print(entries)

	v_best = [0,0]
	curr = simulate([0,0], entries)
	for i in range(x_min):
		for j in range(x_min):
			v_new = [i, j]
			sim_val = simulate(v_new, entries)
			if sim_val > curr:
				v_best = v_new
				curr = sim_val

	return curr

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

