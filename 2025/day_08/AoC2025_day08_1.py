"""
Solution to Advent of Code 2025 day 8 part 1

Solved by finding distances between all pairs and sorting, then using the union-find datastructure to join the circuit sets, and finally a Counter on the union-finde's indices to finish finding the sizes of the circuits.
More elegant solution would have been to find the 10 nearest points with an efficient nearest neighbors algorithm, then finish up with the union-find.
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

	N = 1000

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
	for d, i,j in q[:N]:
		UF.union(i,j)

	for i in range(l):
		UF.find(i)
	
	sizes = sorted(Counter(UF.indices).values(), reverse=True)

	#print(sizes[:3])
	return math.prod(sizes[:3])


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

