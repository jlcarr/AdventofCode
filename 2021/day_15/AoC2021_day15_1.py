"""
Solution to Advent of Code 2021 day 15 part 1

Used NetworkX to perform Dijkstra. Graph was a digraph where edge weight was the cost of entering a node.
Could have also implemented by hand using heapq
"""
import time
import sys

import re
import numpy as np
import networkx as nx

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	entries = [[int(j) for j in e] for e in entries]
	entries = np.array(entries)
	#print(entries)

	# Parse into a graph
	G = nx.DiGraph()
	for i in range(entries.shape[0]):
		for j in range(entries.shape[1]):
			for ip in [-1,1]:
				if entries.shape[0] > i+ip >=0:
					G.add_edge((i,j),(i+ip,j),weight=entries[i+ip,j])
			for jp in [-1,1]:
				if entries.shape[1] > j+jp >=0:
					G.add_edge((i,j),(i,j+jp),weight=entries[i,j+jp])
	# Compute the solution
	path = nx.dijkstra_path(G, (0,0), (entries.shape[0]-1,entries.shape[1]-1))
	weights = [entries[p] for p in path[1:]]
	#print(path)
	#print(weights)
	#print(G.edges())
	return sum(weights)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

