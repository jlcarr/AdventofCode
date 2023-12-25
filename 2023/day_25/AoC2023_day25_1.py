"""
Solution to Advent of Code 2023 day 25 part 1

Solved using NetworkX to find the minimum cut, and the itertools library to go over each combination of start and end pairs for the flow, checking each one if the cut value was 3 edges, and the partition was size 2.
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

import networkx as nx
from itertools import combinations


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [e.split(': ') for e in entries]
	entries = [(e[0],e[1].split()) for e in entries]
	#print(entries)

	G = nx.Graph()
	for s,ts in entries:
		for t in ts:
			G.add_edge(s,t)
	#print(G)
	#print(nx.to_dict_of_dicts(G))
	
	edges = list(G.edges)
	nodes = list(G.nodes)
	for e in edges:
		G.edges[e]['capacity'] = 1
	for ns in combinations(nodes,2): #e1,e2,e3
		cut_value, partition = nx.minimum_cut(G,ns[0],ns[1])
		partition = list(partition)
		if cut_value == 3 and len(partition) == 2:
			#print(cut_value, partition)
			return len(partition[0]) * len(partition[1])
	return None

	
	edges = list(G.edges)
	for es in combinations(edges,3): #e1,e2,e3
		#print(e1)
		#if len({e1,e2,e3} & {('hfx','pzl'), ('cmg','bvb'), ('nvd','jqt')}) >= 1:
		#	print('X')
		#if len({e1,e2,e3} & {('hfx','pzl'), ('bvb','cmg'), ('nvd','jqt')}) == 3:
		#	print(e1,e2,e3)
		for s,t in es:
			G.remove_edge(s,t)
		cc = list(nx.connected_components(G))
		if len(cc) == 2:
			return len(cc[0]) * len(cc[1])
		for s,t in es:
			G.add_edge(s,t)

	return None

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

