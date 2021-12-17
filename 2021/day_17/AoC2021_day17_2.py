"""
Solution to Advent of Code 2021 day 17 part 2

Brute forced by searching in a reasonable radius of all starting values that hit the target.
Again, some proper use of math could have simplified things greatly.
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

	count = 0

	search_r = x_min

	v = (x_min,y_min)
	neighbors_queue = [v]
	checked = set(neighbors_queue)
	while neighbors_queue:
		v = neighbors_queue.pop()
		sim_val = simulate(list(v), entries)
		#print(v, sim_val)
		if sim_val > -1:
			#print(v, len(neighbors_queue))
			count += 1
			for i in range(-search_r,search_r+1):
				for j in range(-search_r,search_r+1):
					v_new = (v[0]+i, v[1]+j)
					if v_new not in checked:
						neighbors_queue.append(v_new)
						checked.add(v_new)
	#print(count, neighbors_queue)

	return count

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

