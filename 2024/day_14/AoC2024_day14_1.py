"""
Solution to Advent of Code 2024 day 14 part 1

Solved using modular arithmetic to instantly compute the final position of each robot and then using some quick comparators to sum up the quadrants.
"""
import time
import sys

# tools
import re

import numpy as np
import scipy.ndimage

from collections import Counter
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [re.findall(r'p=(\-?\d+),(\-?\d+) v=(\-?\d+),(\-?\d+)',e)[0] for e in entries]
	entries = [tuple(map(int,e)) for e in entries]
	#print(entries)
	
	# Solving
	w,h = 11,7
	w,h = 101,103
	pfs = []
	for px,py, vx,vy in entries:
		fx,fy = (px+vx*100)%w, (py+vy*100)%h
		pfs.append((fx,fy))
	#print(pfs)
	
	mx,my = w//2, h//2
	quads = [0]*4
	for x,y in pfs:
		if x == mx or y == my:
			continue
		quads[2*int(y > my) + int(x > mx)] += 1
	
	result = 1
	for q in quads:
		result *= q
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

