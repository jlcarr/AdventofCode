"""
Solution to Advent of Code 2024 day 4 part 2

Solved by first turning the array into `ord` integers, then using SciPy's `scipy.ndimage.generic_filter` to check the `"MAS"` cross at every point, then sum the hits.
"""
import time
import sys

# tools
import numpy as np
import scipy.ndimage


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	entries = [list(map(ord,e)) for e in entries]
	entries = np.array(entries)

	# Solution
	kern = np.ones((3,3), dtype=int)
	def conv_func(arr):
		arr = arr.reshape((3,3)).astype(int)
		uldr = ''.join([chr(arr[i,i]) for i in range(3)])
		urdl = ''.join([chr(arr[i,2-i]) for i in range(3)])
		#print(uldr,urdl)
		if uldr in ["MAS","SAM"] and urdl in ["MAS","SAM"]:
			return True
		return False
	entries = scipy.ndimage.generic_filter(entries, conv_func, footprint=kern, mode='constant', cval=0)
	#print(entries)
	return entries.sum()
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

