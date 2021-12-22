"""
Solution to Advent of Code 2021 day 22 part 2

Find intersecting rectangular prisms, keep track of those whose volumes are added, and subtracted. Doesn't work on the second example, but works on the actual input?
Another approach is to break the added cuboid into rectangular prisms (by shaving off intersections and splitting the rest) and only save those with no intersections.
"""
import time
import sys

import re
import numpy as np
from collections import defaultdict

def intersection_rect(instruc, rect):
	x_min = max(instruc[0], rect[0])
	x_max = min(instruc[1], rect[1])
	if x_min > x_max:
		return None
	y_min = max(instruc[2], rect[2])
	y_max = min(instruc[3], rect[3])
	if y_min > y_max:
		return None
	z_min = max(instruc[4], rect[4])
	z_max = min(instruc[5], rect[5])
	if z_min > z_max:
		return None
	return (x_min,x_max,y_min,y_max,z_min,z_max)

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
	#print(len(entries))

	rect_adders = defaultdict(lambda: 0)
	rect_subbers = defaultdict(lambda: 0)
	for step,instruc in enumerate(entries):
		on_off = instruc[0]
		instruc = instruc[1:]
		# Process
		# Adders
		new_subbers = defaultdict(lambda: 0)
		for rect,count in rect_adders.items():
			intersect = intersection_rect(instruc, rect)
			if intersect:
				new_subbers[intersect] += count
		# Subbers
		new_adders = defaultdict(lambda: 0)
		for rect,count in rect_subbers.items():
			intersect = intersection_rect(instruc, rect)
			if intersect:
				new_adders[intersect] += count
		# Finalize
		if on_off=='on':
			new_adders[tuple(instruc)] += 1
		for key,count in new_adders.items():
			rect_adders[key] += count
		for key,count in new_subbers.items():
			rect_subbers[key] += count
		#print("step", step+1)
		#print("adders", rect_adders)
		#print("subbers", rect_subbers)
		#if step==2:
		#	break

	adder_sum = sum([(x_max-x_min+1)*(y_max-y_min+1)*(z_max-z_min+1)*rect_adders[(x_min,x_max,y_min,y_max,z_min,z_max)] for x_min,x_max,y_min,y_max,z_min,z_max in rect_adders])
	subber_sum = sum([(x_max-x_min+1)*(y_max-y_min+1)*(z_max-z_min+1)*rect_subbers[(x_min,x_max,y_min,y_max,z_min,z_max)] for x_min,x_max,y_min,y_max,z_min,z_max in rect_subbers])
	#print(rect_adders)
	#print(rect_subbers)
	return adder_sum-subber_sum

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

