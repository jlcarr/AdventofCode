"""
Solution to Advent of Code 2025 day 8 part 2

Solved similarly to part 1, but using the logic of Prim's algorithm to notice we can run through trying all pairs, and simply only use the last pair that isn't part of the same set.
A more elegant solution would have been to iteratively add points with nearest neighbors algorithms like in part 1, and also keep track of the union-find set sizes so we know when to stop: set size contains all.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage
import scipy.spatial

from collections import Counter, deque
from functools import cache
import heapq
import math


class UnionFind:
	def __init__(self, n):
		self.indices = list(range(n))
	
	def find(self, v):
		if self.indices[v] != v:
			self.indices[v] = self.find(self.indices[v])
		return self.indices[v]

	def union(self, v1, v2):
		set1, set2 = self.find(v1), self.find(v2)
		if set1 == set2:
			return False
		if set1 < set2:
			self.indices[set2] = set1
		else:
			self.indices[set1] = set2
		return True

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(map(int, e.split(','))) for e in entries]
	l = len(entries)
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	#entries = np.array(entries)
	#print(entries)


	# Solving

	#t = scipy.spatial.KDTree(entries)
	# dd, ii = t.query(n k=2)

	q = []
	for i,a in enumerate(entries):
		for j, b in enumerate(entries[i+1:]):
			d = sum([(aa-bb)**2 for aa,bb in zip(a,b)])
			q.append((d, i,i+1+j))
	
	q.sort()
	#print(q[:10])

	UF = UnionFind(l)

	i_f, j_f = 0,0
	for d, i,j in q:
		if UF.union(i,j):
			i_f, j_f = i, j

	return entries[i_f][0] * entries[j_f][0]


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

