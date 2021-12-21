"""
Solution to Advent of Code 2021 day 20 part 1

Used numpy's padding to account for growth, and generic_filter to apply the transform, with the bounday values being fed to the filter and kept track of.
This one has a trick that the infinite grid all flips.
"""
import time
import sys

import re
import numpy as np
import scipy.ndimage

from PIL import Image

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
	N = 2
	img = np.pad(img,N,mode='constant',constant_values=0)
	#Image.fromarray(255*img.astype(np.uint8)).save('test.png')
	exteriors = 0
	for step in range(N):
		img = scipy.ndimage.filters.generic_filter(img, pick_filter, footprint=kern, mode='constant', cval=exteriors)
		exteriors = pick_filter(exteriors*np.ones(9))

		#new_img = np.zeros(img.shape, dtype=int)
		#for i in range(1, img.shape[0]-1):
		#	for j in range(1, img.shape[1]-1):
		#		arr = np.array([img[i+di, j+dj] for di in [-1,0,1] for dj in [-1,0,1]])
		#		arr = arr.astype(int).astype(str)
		#		bin_string = ''.join(arr)
		#		val = int(bin_string,2)
		#		#print(val)
		#		val = algo[val]
		#		new_img[i,j] = val
		#img = new_img
		#Image.fromarray(255*img.astype(np.uint8)).save(f'test{step}.png')
	#print(img)
	#print(img.shape)
	#Image.fromarray(255*img.astype(np.uint8)).save('test.png')

	return np.sum(img)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

