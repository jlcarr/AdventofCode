"""
Solution to Advent of Code 2023 day 22 part 2

We can determine the pile up without simulating, just by checking which blocks below a given block intersect with it in the xy. By sorting by lowest z value we ensure we process in the right order and get a final a value for each block. For each block we need to check which blocks it could land on and place it 1 space above the max possible final z. We can use the same xy intersection and comparison of final z position to find which blocks are on top of which other. A block with only 1 support means that support can't be disintegrated, so we can count up the essential blocks.
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
	#entries = [int(e) for e in entries]
	entries = [re.findall(r'(\d+),(\d+),(\d+)~(\d+),(\d+),(\d+)',e)[0] for e in entries]
	entries = [tuple(map(int,e)) for e in entries]
	entries = [(e[:3],e[3:]) for e in entries]
	#print(entries)
	#print(len(entries))
	entries.sort(key=lambda x: min(x[0][2], x[1][2]))
	n = len(entries)
	#print(entries)
	
	ontos = []
	finalz_min = []
	finalz_max = []
	for i,((x1,y1,z1),(x2,y2,z2)) in enumerate(entries):
		ontos.append([])
		foundz = 0
		#finalz.append(min(z1,z2))
		for j in range(i-1,-1,-1):
			# check if could be under
			(px1,py1,pz1),(px2,py2,pz2) = entries[j]
			if (min(px1,px2) <= max(x1,x2) and min(x1,x2) <= max(px1,px2)) and \
				(min(py1,py2) <= max(y1,y2) and min(y1,y2) <= max(py1,py2)):
				foundz = max(foundz, finalz_max[j]+1)
		for j in range(i-1,-1,-1):
			(px1,py1,pz1),(px2,py2,pz2) = entries[j]
			if (min(px1,px2) <= max(x1,x2) and min(x1,x2) <= max(px1,px2)) and \
				(min(py1,py2) <= max(y1,y2) and min(y1,y2) <= max(py1,py2)):
				if foundz == finalz_max[j]+1:
					ontos[i].append(j)
		finalz_min.append(foundz)
		finalz_max.append(abs(z2-z1) + foundz)
	
	#print(finalz_min)
	#print(ontos)
	
	can_del = [True]*n
	for i,v in enumerate(ontos):
		if len(v) == 1:
			can_del[v[0]] = False
	#print(can_del)

	return sum(can_del)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

