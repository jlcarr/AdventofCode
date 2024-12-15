"""
Solution to Advent of Code 2024 day 14 part 2

Solved using numpy and Pillow to make pngs of the different steps and look for patterns. Noticed vertical oddities every 33+101a and horizontal oddities every 87+103b. Used z3 to solve the Bezout's identity. A more general way perhaps to find the Easter egg would have been to use a convolutional filter to check for when an image have large contiguous blocks and robots instead of scattered.
"""
import time
import sys

# tools
import re

import numpy as np
#import scipy.ndimage
from PIL import Image

import z3

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [re.findall(r'p=(\-?\d+),(\-?\d+) v=(\-?\d+),(\-?\d+)',e)[0] for e in entries]
	entries = [tuple(map(int,e)) for e in entries]
	#print(entries)
	#print(len(entries))
	
	w,h = 11,7
	w,h = 101,103
	imgs = []
	for t in range(100): # (33,1000,101) (87,1000,103)
		pfs = [((px+vx*t)%w, (py+vy*t)%h) for px,py, vx,vy in entries]
		arr = np.zeros((h,w), dtype=np.uint8)
		for x,y in pfs:
			arr[y,x] = 255
		img = Image.fromarray(arr)
		#img.save(f'{t}.png')
		
	# oddities at 33, 87, 134, 190, 235, 293, 336, 396
	# vertical at 33, 134, 235, 336 -> diff 101
	# horizontal at 87, 190, 293, 396 -> diff 103

	
	# 33 + 101*a = 87 + 103*b
	solver = z3.Solver()
	a = z3.Int('a')
	b = z3.Int('b')
	solver.add(a >= 0)
	solver.add(b >= 0)
	solver.add(33 + 101*a == 87 + 103*b)
	if solver.check() == z3.sat:
		model = solver.model()
		sol =  model.eval(33 + 101*a).as_long()
		# print the final picture
		pfs = [((px+vx*sol)%w, (py+vy*sol)%h) for px,py, vx,vy in entries]
		arr = np.zeros((h,w), dtype=np.uint8)
		for x,y in pfs:
			arr[y,x] = 255
		img = Image.fromarray(arr)
		#img.save(f'sol_{t}.png')
		return sol
	return None


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

