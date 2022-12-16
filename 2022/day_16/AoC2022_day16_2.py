"""
Solution to Advent of Code 2022 day 16 part 2

Similar to part 1, but using the insight that the valves you and the elephant visit will be independent, and so we can run the same BFS on masks and complements of all non-zero valves and take the sum. Caching by current valve, time remaining and valve states, makes this go much faster.
My original idea was to use 2 agents in parallel, but to give them cooldowns.
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
from itertools import product

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
	inv = dict()
	for i,(f,ts) in enumerate(entries):
		t,f = f
		fs[t] = int(f)
		for t2 in ts:
			G.add_edge(t,t2)
		#G[t] = ts
		index_map[t] = i
		inv[i] = t
	dists = dict(nx.all_pairs_shortest_path_length(G))
	
	#print(fs)
	#print()

	# Solving
	
	@cache
	def search(curr, t_rem, state):
		state = list(state)
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
				sub_sol,sub_chain = search(neighbor, t_rem, tuple(state))
				if sub_sol + new_flow > sol:
					sol = sub_sol + new_flow
					chain = sub_chain
				state[i] = False
				t_rem += d + 1
		return sol, []#[curr] + chain
		
	states = [[]]
	for i in range(len(fs)):
		v = fs[inv[i]]
		if v == 0:
			states = [state + [False] for state in states]
		else:
			states = [state + [False] for state in states] + [state + [True] for state in states]

	#print(len(states))
	result = 0
	for i,state in enumerate(states):
		#if i % 100 == 0:
		#print(i)
		sub_sol = search('AA', 26, tuple([x for x in state]))[0]
		complement_sol = search('AA', 26, tuple([not x for x in state]))[0]
		result = max(result, sub_sol + complement_sol)
		
	return result

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

