"""
Solution to Advent of Code 2023 day 17 part 2

Same as part 1, but made it a count-up instead of down, and used that to filter states.
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

import heapq

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [[int(c) for c in e] for e in entries]
	#print(entries)
	rows,cols = len(entries), len(entries[0])

	q = [(0,0,0,0,0,0)]
	searched = set()
	
	while q:
		cost,r,c,dr,dc, countdown = heapq.heappop(q)
		if r == rows-1 and c == cols-1:
			return cost
		for pr,pc in [(r-1,c),(r+1,c),(r,c-1),(r,c+1)]:
			if pr-r == -dr and pc-c == -dc:
				continue
			pcountdown = countdown+1 if pr-r == dr and pc-c == dc else 0
			if pcountdown >= 10:
				continue
			if not (dr == 0 and dc == 0) and countdown < 4-1 and pcountdown == 0:
				continue
			if (0 <= pr < rows) and (0 <= pc < cols) and (pr,pc, pr-r,pc-c, pcountdown) not in searched:
				heapq.heappush(q, (cost+entries[pr][pc], pr,pc, pr-r,pc-c, pcountdown))
				searched.add((pr,pc, pr-r,pc-c, pcountdown))
	return -1


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

