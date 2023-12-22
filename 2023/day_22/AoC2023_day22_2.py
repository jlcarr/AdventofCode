"""
Solution to Advent of Code 2023 day 22 part 2

Similar computation of block order as part 1, but inverting the mapping of blocks into others gives which blocks a given block supports. For each block we need to search for which blocks will fall if removed in order: use a heap as a priority queue by max z height, so as to ensure we process all supports of a given block before the block itself to see if it falls.
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
			#if max(pz1,pz2) > min(z1,z2):
			#	continue
			#if foundz is not None and finalz_max[j]+1 != foundz:
			#	break
			# check crossing
			if (min(px1,px2) <= max(x1,x2) and min(x1,x2) <= max(px1,px2)) and \
				(min(py1,py2) <= max(y1,y2) and min(y1,y2) <= max(py1,py2)):
				#if foundz is None:
				#	foundz = finalz_max[j]+1
				foundz = max(foundz, finalz_max[j]+1)
				#if foundz == finalz_max[j]+1:
				#	ontos[i].append(j)
		for j in range(i-1,-1,-1):
			(px1,py1,pz1),(px2,py2,pz2) = entries[j]
			if (min(px1,px2) <= max(x1,x2) and min(x1,x2) <= max(px1,px2)) and \
				(min(py1,py2) <= max(y1,y2) and min(y1,y2) <= max(py1,py2)):
				if foundz == finalz_max[j]+1:
					ontos[i].append(j)
		#if foundz is None:
		#	foundz = 0
		finalz_min.append(foundz)
		finalz_max.append(abs(z2-z1) + foundz)
	
	#print(finalz_min)
	#print(ontos)
	
	invontos = [[] for i in range(n)]
	for i,v in enumerate(ontos):
		for j in v:
			invontos[j].append(i)
	#print(invontos)
	ontos = [set(v) for v in ontos]
	
	sol = 0
	collapses = dict()
	for d,starts in enumerate(invontos):
		q = [(finalz_max[i],i) for i in starts]
		found = set(starts)
		found.add(d)
		collapsed = set([d])
		while q:
			z,curr = heapq.heappop(q)
			if ontos[curr].issubset(collapsed):
				collapsed.add(curr)
				for i in invontos[curr]:
					found.add(i)
					heapq.heappush(q, (finalz_max[i], i))
		collapses[d] = len(collapsed) - 1

	#print(ontos)
		
	#print(collapses)

	return sum(collapses.values())

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

