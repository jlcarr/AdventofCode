"""
Solution to Advent of Code 2021 day 8 part 2

Ended up just using brute force since the 7 segments means 7!=5040 possibilities for each entry.
There's probably a faster solution using set comparisons and logical deduction, but coding that up has not been easy.
"""
import time
import sys

import re
from itertools import permutations

segments = [
	'abcefg',
	'cf',
	'acdeg',
	'acdfg',
	'bcdf',
	'abdfg',
	'abdefg',
	'acf',
	'abcdefg',
	'abcdfg'
]
segs_to_dig = {seg:n for n,seg in enumerate(segments)}

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	entries = [[[set(dig) for dig in side.split()] for side in e.split(' | ')] for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	#entries = np.array(entries)
	#print(entries)
	

	sol = 0
	for e in entries:
		for perm in permutations('abcdefg'):
			#perm = 'deafgbc'
			seg_map = {fake_seg:true_seg for fake_seg,true_seg in zip(perm,'abcdefg')}
			unmapped_digit_segs = [''.join(sorted([seg_map[seg] for seg in digit])) for digit in e[0]]
			#print(seg_map)
			#print(unmapped_digit_segs)
			#print([segs_to_dig[segs] for segs in unmapped_digit_segs])
			
			if set(segments) == set(unmapped_digit_segs):
				qsol = 0
				for digit in e[1]:
					qsol *= 10
					qsol += segs_to_dig[''.join(sorted([seg_map[seg] for seg in digit]))]
				sol += qsol
				break

		#sol+= len([dig for dig in e[1] if len(dig) in [2, 4, 3,7]])

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

