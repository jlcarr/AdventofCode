"""
Solution to Advent of Code 2021 day 20 part 2

Same as part 1.
"""
import time
import sys

import re
import numpy as np
import scipy.ndimage

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	algo, img = entries.split('\n\n')
	algo = ''.join(algo.splitlines())
	algo = algo.strip()
	algo = [col=='#' for col in algo]
	algo = np.array(algo).astype(int)

	img = img.splitlines()
	img = [[col=='#' for col in row] for row in img]
	img = np.array(img).astype(int)
	
	#print(algo)
	#print(len(algo))
	#print(img)
	#print(img.shape)

	def pick_filter(arr):
		arr = arr.astype(int).astype(str)
		bin_string = ''.join(arr)
		val = int(bin_string,2)
		#print(val)
		val = algo[val]
		return val

	kern = np.ones((3,3), dtype=int)

	# Main
	N = 50
	img = np.pad(img,N,mode='constant',constant_values=0)
	exteriors = 0
	for step in range(N):
		#print(step)
		img = scipy.ndimage.filters.generic_filter(img, pick_filter, footprint=kern, mode='constant', cval=exteriors)
		exteriors = pick_filter(exteriors*np.ones(9))

	return np.sum(img)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

