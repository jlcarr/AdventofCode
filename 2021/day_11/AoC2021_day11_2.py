"""
Solution to Advent of Code 2021 day 11 part 2

Same as part 1, just letting it run until the synchronize step is found.
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
	step = 0
	while True:
		step += 1
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
		if not np.any(entries):
			break

	#print(entries)
	return step

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

