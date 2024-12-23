"""
Solution to Advent of Code 2024 day 23 part 1

Solved using using NetworkX to build the graph and itertools to iterate over all pairs of neighbors for each node, and keep the valid sorted triples in a set for counting. My original slower approach was to iterate over all combinations of 3 nodes and check if they all have edges.
"""
import time
import sys

# tools
import itertools
import networkx as nx


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [e.split('-') for e in entries]
	#print(entries)

	# Setup
	G = nx.Graph()
	for u,v in entries:
		G.add_edge(u,v)

	# Solving
	
	# older slower solution
	#result = 0
	#for trio in itertools.combinations(G.nodes(),3):
	#	if any(i[0] == 't' for i in trio) and all(G.has_edge(i,j) for i,j in itertools.combinations(trio,2)):
	#		result += 1
	
	result = set()
	for i in G.nodes():
		if i[0] != 't':
			continue
		for j,k in itertools.combinations(G.neighbors(i),2):
			if G.has_edge(j,k):
				result.add(tuple(sorted((i,j,k))))
	return len(result)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

