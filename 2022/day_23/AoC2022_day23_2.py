"""
Solution to Advent of Code 2022 day 23 part 2

Same as part 1, but letting the loop continue until the counts of proposed positions turned up 0.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage

from collections import Counter, deque
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	entries = np.array(entries)
	#for row in entries:
	#	print(''.join(row))
	#print()
	
	#entries = np.pad(entries, 1, mode='constant', constant_values=('.'))
	#for row in entries:
	#	print(''.join(row))
	#print()

	# Solving
	choice_order = [(-1,0), (1,0), (0,-1), (0,1)]
	
	#kern = np.ones((3), dtype=int)
	#def conv_func(arr):
	#	arr = arr.reshape((3))
	#	return arr[1]
	#entries = scipy.ndimage.filters.generic_filter(entries, conv_func, footprint=kern, mode='constant', cval=0)
	
	round = 0
	
	while True:
		top_pad = int((entries[0,:] == '#').any())
		bottom_pad = int((entries[-1,:] == '#').any())
		left_pad = int((entries[:,0] == '#').any())
		right_pad = int((entries[:,-1] == '#').any())
		entries = np.pad(entries, ((top_pad,bottom_pad),(left_pad,right_pad)), mode='constant', constant_values=('.'))
		#entries = np.pad(entries, 1, mode='constant', constant_values=('.'))
		#for row in entries:
		#	print(''.join(row))
		#print()
		m,n = entries.shape
		counts = np.zeros((m,n), dtype=int)
		for i in range(m):
			for j in range(n):
				if entries[i,j] == '#' and any(entries[i+ik,j+jk]=='#' for ik in [-1,0,1] for jk in [-1,0,1] if not (jk==0 and ik==0)):
					for choice in choice_order:
						if all(entries[i+choice[0]+k*choice[1], j+k*choice[0]+choice[1]] == '.' for k in [-1,0,1]):
							counts[i+choice[0],j+choice[1]] += 1
							break
		if counts.sum() == 0:
			break
		#print(counts)
		# perform the update
		new_entries = np.copy(entries)
		for i in range(m):
			for j in range(n):
				if entries[i,j] == '#' and any(entries[i+ik,j+jk]=='#' for ik in [-1,0,1] for jk in [-1,0,1] if not (jk==0 and ik==0)):
					for choice in choice_order:
						if all(entries[i+choice[0]+k*choice[1], j+k*choice[0]+choice[1]] == '.' for k in [-1,0,1]):
							if counts[i+choice[0], j+choice[1]] == 1:
								new_entries[i,j] = '.'
								new_entries[i+choice[0], j+choice[1]] = '#'
							break
		entries = new_entries
		choice_order = choice_order[1:] + [choice_order[0]]
		round += 1
		#print(round)
				
		#for row in entries:
		#	print(''.join(row))
		#print()

	# shave
	while not (entries[0,:]=='#').any():
		entries = entries[1:,:]
	while not (entries[-1,:]=='#').any():
		entries = entries[:-1,:]
	while not (entries[:,0]=='#').any():
		entries = entries[:,1:]
	while not (entries[:,-1]=='#').any():
		entries = entries[:,:-1]
	
	#for row in entries:
	#	print(''.join(row))
	#print()
	
	return round+1

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

