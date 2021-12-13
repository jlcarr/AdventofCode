"""
Solution to Advent of Code 2021 day 13 part 2

Same as day 1, but had to add a function to print the final result.
"""
import time
import sys

import re
import numpy as np


def sol_printer(points):
	points = set(points)
	max_x = max([p[0] for p in points])
	max_y = max([p[1] for p in points])

	for y in range(max_y+1):
		for x in range(max_x+1):
			if (x,y) in points:
				print("#",end="")
			else:
				print(".",end="")
		print("\n",end="")

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
		points = new_points
	sol_printer(points)
	return None

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

