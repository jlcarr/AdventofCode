"""
Solution to Advent of Code 2021 day 13 part 1

Reflected all coordinates over the folds and used a set for uniqueness.
"""
import time
import sys

import re
import numpy as np


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	points, folds = entries.split('\n\n')
	points = points.splitlines()
	folds = folds.splitlines()
	points = [p.split(',') for p in points]
	points = [[int(i) for i in p] for p in points]
	folds = [f.split(' ')[-1].split('=') for f in folds]
	#print(points)
	#print(folds)

	sol = 0
	for f_d,f_p in folds:
		f_p = int(f_p)
		new_points = []
		for p_x,p_y in points:
			if f_d == 'x' and p_x > f_p:
				p_x = f_p - (p_x-f_p)
			if f_d == 'y' and p_y > f_p:
				p_y = f_p - (p_y-f_p)
			if (p_x,p_y) not in new_points:
				new_points.append((p_x,p_y))
		#print(new_points)
		sol = len(new_points)
		break

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

