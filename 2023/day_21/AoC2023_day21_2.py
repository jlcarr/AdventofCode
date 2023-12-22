"""
Solution to Advent of Code 2023 day 21 part 2

Because of the repeating tile structure and Manhattan distance traversal, we eventually reach a point where the expanding diamond's edges will be the same along a side, and an increase of steps by a tile length will just add more tiles to the interior without changing the repeated structure of the edges. For the input we also have an "air gap" which makes it converge faster. Since the "area" covered will be proportional to the square of the distance, we can fit a quadratic and extrapolate. We take samples starting from the remainder with the target, then at every period equal to a tile length, and check for the point at which the 3rd difference is 0, indicating we have reached the polynomial regularity. Use a Lagrange polynomial for an exact fit.
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

from scipy.interpolate import lagrange

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#entries = np.array(entries)
	#print(entries)

	rows,cols = len(entries), len(entries[0])
	#print(rows,cols)

	start = None
	for i in range(rows):
		for j in range(cols):
			if entries[i][j] == 'S':
				start = (i,j)
				break
	#print(start)
	
	target = 26501365
	trem = target % rows
	
	q = {(0,0): set([start])}

	steps = []
	vals = []
	step = 0
	while True:
		step += 1
		#print(step)
		newq = dict()
		for mi,mj in q.keys():
			for (i,j) in q[(mi,mj)]:
				for ip,jp in [(i+1,j),(i-1,j),(i,j+1),(i,j-1)]:
					mip,mjp = mi,mj
					# fix map piece
					if ip < 0:
						mip -= 1
					if ip >= rows:
						mip += 1
					if jp < 0:
						mjp -= 1
					if jp >= cols:
						mjp += 1
					# fix coords
					ip %= rows
					jp %= cols
					# dont take rocks
					if entries[ip][jp] == '#':
						continue
					# add if not there
					if (mip,mjp) not in newq:
						newq[(mip,mjp)] = set()
					# finally add
					newq[(mip,mjp)].add((ip,jp))
		q = newq
		if (step - trem) % rows == 0:
			vals.append(sum(len(v) for v in q.values()))
			steps.append(step)
			#print(steps,vals)
		if len(vals) >= 1+3 and np.array(np.diff(vals,3))[-1] == 0:
			break
			
	#print(vals, steps, np.array(np.diff(vals,2)))
	poly = lagrange(steps[-3:], vals[-3:])
	
	return int(round(poly(target)))


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

