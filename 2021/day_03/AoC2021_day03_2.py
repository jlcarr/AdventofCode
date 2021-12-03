"""
Solution to Advent of Code 2021 day 3 part 2

Solved using numpy's summation along a chosen axis, plus numpy's masking, plus binary conversion.
Should have used int(''.join(map(str,entries)), 2) to convert binary to decimal
"""
import time
import sys

import re
import numpy as np

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	entries = [[int(j) for j in e] for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	entries = np.array(entries)
	length = entries.shape[1]

	# copied for later
	copy = np.copy(entries)
	# go over the bits, and filter the entries by those matching the majority bitset
	for bit in range(length):
		maj = entries.sum(axis=0)>=entries.shape[0]/2
		mask = entries[:,bit] == maj[bit]
		entries = entries[mask,:]
		if entries.shape[0] == 1:
			break
	# convert the result from binary to decimal
	entries = list(entries[0])
	oxy= 0
	num = 1
	for i,b in enumerate(entries[::-1]):
		if b:
			oxy += num
		num *= 2

	# restore the copied array
	entries = copy
	# go over the bits, and filter the entries by those matching the minority bitset
	for bit in range(length):
		maj = entries.sum(axis=0)<entries.shape[0]/2
		mask = entries[:,bit] == maj[bit]
		entries = entries[mask,:]
		if entries.shape[0] == 1:
			break
	# convert the result from binary to decimal
	entries = list(entries[0])
	co= 0
	num = 1
	for i,b in enumerate(entries[::-1]):
		if b:
			co += num
		num *= 2

	return co*oxy

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

