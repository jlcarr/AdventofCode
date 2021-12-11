"""
Solution to Advent of Code 2021 day 11 part 1

Solved using a mask to find new flashes, and convolving to find the effect of the flash. Repeat on each step to get fixed points.
could have also been solved with a regular convolution.
"""
import time
import sys

import re
import numpy as np
import scipy.ndimage
from scipy import signal

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	entries = [[int(j) for j in e] for e in entries]
	entries = np.array(entries)
	#print(entries)

	kern = np.ones((3,3))
	kern[1,1] = 0

	sol = 0
	for i in range(100):
		#print(entries)
		entries += 1
		flash_mask = np.zeros(entries.shape).astype(bool)
		change = True
		while change:
			new_flash = (entries > 9) & ~flash_mask
			sol += np.sum(new_flash)
			change = np.any(new_flash)
			update = scipy.ndimage.filters.generic_filter(new_flash.astype(int), np.sum, footprint=kern, mode='constant')
			flash_mask |= new_flash
			entries += update
			#print("newflash")
			#print(new_flash.astype(int))
			#print(update)
			#print(flash_mask.astype(int))
			#print(change)
			#break
		entries *= (entries < 10)

	#print(entries)
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

