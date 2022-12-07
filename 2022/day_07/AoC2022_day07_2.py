"""
Solution to Advent of Code 2022 day 7 part 2

Same as part 1, but with less to compute, and using a global dict of directory sizes to finally run through to find the optimal directory to delete.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage

from collections import Counter
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	#print(entries)

	# Solving

	root = dict()
	curr = root
	sol = 0
	for i,l in enumerate(entries):
		#print(root)
		l = l.split(' ')
		# listed
		if l[0] != '$':
			if l[0] == 'dir':
				if l[1] not in curr:
					curr[l[1]] = dict()
					curr[l[1]]['..'] = curr
				continue
			curr[l[1]] = int(l[0])
			continue
		# command
		if l[1] == 'cd':
			if l[2] == '/':
				curr = root
				continue
			elif l[2] not in curr:
				curr[l[2]] = dict()
				curr[l[2]]['..'] = curr
			curr = curr[l[2]]
		elif l[1] == 'ls':
			continue
	#print(root) #json.dumps(root, indent=4)
		
	dir_map = dict()
	def rec(curr, dir_name):
		dir_size = 0
		for k,v in curr.items():
			if k == '..':
				continue
			if isinstance(v, dict):
				sub_size = rec(v, k)
				dir_size += sub_size
			else:
				dir_size += v
		#if dir_size <= 100000:
		dir_map[dir_name] = dir_size
		return dir_size
		
	dir_size = rec(root, '/')
	#print(dir_map)
	
	remaining = 70000000 - dir_size
	needed = 30000000 - remaining
	
	if needed <= 0:
		return None
	
	return min([(v,k) for k,v in dir_map.items() if v >= needed])[0]

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

