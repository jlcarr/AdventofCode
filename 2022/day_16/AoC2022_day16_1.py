"""
Solution to Advent of Code 2022 day 16 part 1

Solved by first using NetworkX to find the distances between all pairs of tunnels. It is now a problem of finding the optimal ordering of the valves to open. Then the key insight to making the problem computationally feasible is to notice that most of the valves have a flow-rate of 0 and can be ignored. Perform a DFS keeping track of the current location, the time and the state of the valves.
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


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	flow_rates = [re.findall(r'Valve (..) has flow rate=(\d+);',e)[0] for e in entries]
	tunnels = [e.split('valve')[-1][1:].strip().split(', ') for e in entries]
	entries = list(zip(flow_rates, tunnels))
	#print(json.dumps(entries, indent=4))
	#print(flow_rates)
	#print(tunnels)
	
	fs = dict()
	G = nx.DiGraph()
	#G = dict()
	index_map = dict()
	for i,(f,ts) in enumerate(entries):
		t,f = f
		fs[t] = int(f)
		for t2 in ts:
			G.add_edge(t,t2)
		#G[t] = ts
		index_map[t] = i
	dists = dict(nx.all_pairs_shortest_path_length(G))
	
	#print(fs)
	#print()

	# Solving
	state = [False] * len(fs)
	
	def search(curr, t_rem):
		sol = 0
		chain = []
		for neighbor in fs.keys():
			i = index_map[neighbor]
			if state[i] or fs[neighbor] == 0:
				continue
			d = dists[curr][neighbor]
			if d < t_rem:
				t_rem -= d + 1
				state[i] = True
				new_flow = t_rem * fs[neighbor]
				sub_sol,sub_chain = search(neighbor, t_rem)
				if sub_sol + new_flow > sol:
					sol = sub_sol + new_flow
					chain = sub_chain
				state[i] = False
				t_rem += d + 1
		return sol, []#[curr] + chain

	return search('AA', 30)[0]

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

