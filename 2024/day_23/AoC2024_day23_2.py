"""
Solution to Advent of Code 2024 day 23 part 2

Solved using NetworkX to find all maximal cliques and then we can take the max clique. While the problem is NP-Complete, for this particular graph, NetworkX's algorithm runs quickly.
"""
import time
import sys

# tools
import networkx as nx


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [e.split('-') for e in entries]
	#print(entries)

	G = nx.Graph()
	for u,v in entries:
		G.add_edge(u,v)

	#clique = nx.approximation.max_clique(G)
	#print(clique)
	#return ','.join(sorted(clique))
	
	return ','.join(sorted(max(nx.find_cliques(G), key=len)))
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

