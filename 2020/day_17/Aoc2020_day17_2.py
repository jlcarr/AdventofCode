"""
Solution to Advent of Code 2020 day 17 part 2

Same as day 1
"""
import time
import sys

import numpy as np
from scipy import ndimage

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	entries = [[1 if y=='#' else 0 for y in z] for z in entries]
	entries = [[entries]]
	entries = np.array(entries)
	#print(entries)
	#print(entries.shape)
	kern= np.ones((3,3,3,3))
	kern[1,1,1,1] = 0
	#print(kern)
	for c in range(6):
		count = np.pad(entries,1,mode='constant',constant_values=0)
		count = ndimage.convolve(count, kern, mode='constant', cval=0)
		entries = np.pad(entries,1,mode='constant',constant_values=0)
		new = np.zeros(count.shape)
		for i in range(new.shape[0]):
			for j in range(new.shape[1]):
				for k in range(new.shape[2]):
					for l in range(new.shape[3]):
						if entries[i,j,k,l] == 1 and (count[i,j,k,l]==2 or count[i,j,k,l]==3):
							new[i,j,k,l] = 1
						elif entries[i,j,k,l] == 0 and count[i,j,k,l]==3:
							new[i,j,k,l] = 1
						else:
							new[i,j,k,l] = 0
		entries = new
		#print(c)
		#print(new)

	return int(np.sum(entries))

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
