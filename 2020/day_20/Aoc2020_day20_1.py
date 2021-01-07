"""
Solution to Advent of Code 2020 day 19 part 2

Same as day 1, but used finite depth recursion on rules to solve the problem
(i.e. not a general solution)
"""
import time
import sys

import numpy as np


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.split('\n\n')
	print(len(entries))
	t = dict()
	for tile in entries:
		if tile == '':
			continue
		t_k = int(tile.splitlines()[0].split(' ')[1].replace(':',''))
		t_v = np.array([[c=='#' for c in list(row)] for row in tile.splitlines()[1:]], dtype=int)
		print(t_v,t_k)
		t[t_k] = t_v
	#entries = dict([(int(tile.splitlines()[0].split(' ')[1].replace(':','')) , np.array([[c=='#' for c in list(row)] for row in tile.splitlines()[1:]], dtype=int)) for tile in entries])
	entries = t
	#print([ for tile in entries])
	print(next(iter(entries.values())))

	print("search start")
	neighbors = dict()
	for key,val in entries.items():
		neighbors[key] = set()
		for k1,v1 in entries.items():
			if k1 == key:
				continue
			if (val[0,:] == v1[0,:]).all() or (val[0,:] == v1[0,::-1]).all():
				neighbors[key].add(k1)
			if (val[-1,:] == v1[0,:]).all() or (val[-1,:] == v1[0,::-1]).all():
				neighbors[key].add(k1)
			if (val[:,0] == v1[0,:]).all() or (val[:,0] == v1[0,::-1]).all():
				neighbors[key].add(k1)
			if (val[:,-1] == v1[0,:]).all() or (val[:,-1] == v1[0,::-1]).all():
				neighbors[key].add(k1)
			if (val[0,:] == v1[-1,:]).all() or (val[0,:] == v1[-1,::-1]).all():
				neighbors[key].add(k1)
			if (val[-1,:] == v1[-1,:]).all() or (val[-1,:] == v1[-1,::-1]).all():
				neighbors[key].add(k1)
			if (val[:,0] == v1[-1,:]).all() or (val[:,0] == v1[-1,::-1]).all():
				neighbors[key].add(k1)
			if (val[:,-1] == v1[-1,:]).all() or (val[:,-1] == v1[-1,::-1]).all():
				neighbors[key].add(k1)
			if (val[0,:] == v1[:,0]).all() or (val[0,:] == v1[::-1,0]).all():
				neighbors[key].add(k1)
			if (val[-1,:] == v1[:,0]).all() or (val[-1,:] == v1[::-1,0]).all():
				neighbors[key].add(k1)
			if (val[:,0] == v1[:,0]).all() or (val[:,0] == v1[::-1,0]).all():
				neighbors[key].add(k1)
			if (val[:,-1] == v1[:,0]).all() or (val[:,-1] == v1[::-1,0]).all():
				neighbors[key].add(k1)
			if (val[0,:] == v1[:,-1]).all() or (val[0,:] == v1[::-1,-1]).all():
				neighbors[key].add(k1)
			if (val[-1,:] == v1[:,-1]).all() or (val[-1,:] == v1[::-1,-1]).all():
				neighbors[key].add(k1)
			if (val[:,0] == v1[:,-1]).all() or (val[:,0] == v1[::-1,-1]).all():
				neighbors[key].add(k1)
			if (val[:,-1] == v1[:,-1]).all() or (val[:,-1] == v1[::-1,-1]).all():
				neighbors[key].add(k1)
	print(neighbors)
	res = 1
	for tile,n in neighbors.items():
		if len(n)==2:
			print(tile)
			res *= tile
	return res

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
