"""
Solution to Advent of Code 2022 day 16 part 2

This solution uses both agents running at the same time with a cooldown. It seems it takes too long to run.
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
	
	@cache
	def search(curr1, curr2, cooldown1, cooldown2, t_rem, state):
		state = list(state)
		sol = 0
		chain = []
		if cooldown1 <= cooldown2:
			# move time up
			t_rem -= cooldown1
			cooldown2 -= cooldown1
			# look for a new neighbor
			for neighbor in fs.keys():
				i = index_map[neighbor]
				if state[i] or fs[neighbor] == 0:
					continue
				d = dists[curr1][neighbor]
				if d < t_rem:
					state[i] = True
					new_flow = (t_rem-(d + 1)) * fs[neighbor]
					sub_sol,sub_chain = search(neighbor, curr2, d + 1, cooldown2, t_rem, tuple(state))
					if sub_sol + new_flow > sol:
						sol = sub_sol + new_flow
						chain = sub_chain
					state[i] = False
		else:
			# move time up
			t_rem -= cooldown2
			cooldown1 -= cooldown2
			# look for a new neighbor
			for neighbor in fs.keys():
				i = index_map[neighbor]
				if state[i] or fs[neighbor] == 0:
					continue
				d = dists[curr2][neighbor]
				if d < t_rem:
					state[i] = True
					new_flow = (t_rem-(d + 1)) * fs[neighbor]
					sub_sol,sub_chain = search(curr1, neighbor, cooldown1, d + 1, t_rem, tuple(state))
					if sub_sol + new_flow > sol:
						sol = sub_sol + new_flow
						chain = sub_chain
					state[i] = False
		return sol, []#[curr] + chain

	state = [False] * len(fs)
	return search('AA', 'AA', 0, 0, 26, tuple(state))[0]

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

