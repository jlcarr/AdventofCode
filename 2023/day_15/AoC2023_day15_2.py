"""
Solution to Advent of Code 2023 day 15 part 2

This was the perfect opportunity to use Python's OrderedDict class.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage

from collections import Counter, deque, OrderedDict
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()
	entries = entries.replace('\n', '')

	# Parsing
	entries = entries.split(',')
	entries = [e.split('=') if '=' in e else (e.split('-')[0],'-') for e in entries]
	#print(entries)

	# Solving
	
	boxes = [OrderedDict() for _ in range(256)]

	for i,e in enumerate(entries):
		curr = 0
		for c in e[0]:
			curr += ord(c)
			curr *= 17
			curr %= 256
		
		if e[1] == '-':
			if e[0] in boxes[curr]:
				del boxes[curr][e[0]]
		else:
			boxes[curr][e[0]] = int(e[1])
		
		#print(i,e)
		#print([(j,b) for j,b in enumerate(boxes) if b])
		
	sol = 0
	for bnum,box in enumerate(boxes,1):
		for slot, fl in enumerate(box.values(),1):
			#print(bnum,slot,fl, bnum*slot*fl)
			sol += bnum*slot*fl
		
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

