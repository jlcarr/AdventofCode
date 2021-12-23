"""
Solution to Advent of Code 2021 day 23 part 1

Used A* with a bunch of processing to create the graph. States are stored as a tuple of positions, heuristic is cost to positions ignoring blocking. Valid moves are only to the hallway and back.
There must be a faster representation, perhaps using symmetry.
"""
import time
import sys

import re
import numpy as np
import networkx as nx
import heapq


def print_state(entries, state):
	new_map = [['.' if c in 'ABCD' else c for c in row] for row in entries]
	for i,pos in enumerate(state):
		new_map[pos[0]][pos[1]] = 'ABCD'[i//2]
	print('\n'.join([''.join(row) for row in new_map]))

def heuristic(graph, state, targets):
	cost = 0
	for i,c in enumerate('ABCD'):
		cost1 = nx.shortest_path_length(graph, state[2*i], targets[c][0])
		cost1 += nx.shortest_path_length(graph, state[2*i+1], targets[c][1])
		cost2 = nx.shortest_path_length(graph, state[2*i], targets[c][1])
		cost2 += nx.shortest_path_length(graph, state[2*i+1], targets[c][0])
		cost += min((cost1,cost2)) * (10**i)
	return cost

def neighboring_states(graph, state, targets, hallway):
	neighbors = []
	for i,pos in enumerate(state): # i,c in enumerate('AABBCCDD'): # loop over creatures
		# check in move to hallway
		if pos not in hallway:
			# check all possible hallway positions it could move to for blockages
			for dest in hallway:
				path = nx.shortest_path(graph, pos, dest)
				if len([1 for other_pos in state if other_pos != pos and other_pos in path]) == 0:
					# if successful add new state neighbor
					cost = (len(path)-1) * 10**(i//2)
					new_state = list(state)
					new_state[i] = dest
					new_state = tuple(new_state)
					neighbors.append((cost, new_state))
		# check move to room
		else:
			# check able to move to destination
			c = 'ABCD'[i//2]
			# check dest room is clear
			if len([1 for j,other_pos in enumerate(state) if j//2 != i//2 and other_pos in targets[c]]) == 0:
				# Looks for clear paths
				for dest in targets[c]:
					path = nx.shortest_path(graph, pos, dest)
					if len([1 for other_pos in state if other_pos != pos and other_pos in path]) == 0:
						# if successful add new state neighbor
						cost = (len(path)-1) * 10**(i//2)
						new_state = list(state)
						new_state[i] = dest
						new_state = tuple(new_state)
						neighbors.append((cost, new_state))
	return neighbors


def A_star(graph, state, targets, hallway):
	cost_estimate = heuristic(graph, state, targets)

	paths = {state:[state]}
	g_map = {state:0}
	f_map = {state:cost_estimate}

	queue = [(f_map[state], state)]
	heapq.heapify(queue)

	while queue:
		#print(len(queue), f_map[queue[0][1]])
		cost_estimate, state = heapq.heappop(queue)
		if all([pos in targets['ABCD'[i//2]] for i,pos in enumerate(state)]):
			return g_map[state],paths[state]

		# find neighboring states
		for new_cost,new_state in neighboring_states(graph, state, targets, hallway):
			new_cost = new_cost + g_map[state]
			if new_state not in g_map.keys() or new_cost < g_map[new_state]:
				new_cost_estimate = new_cost + heuristic(graph, new_state, targets)
				if new_state not in paths:
					heapq.heappush(queue, (new_cost_estimate, new_state))
				paths[new_state] = paths[state] + [new_state]
				g_map[new_state] = new_cost
				f_map[new_state] = new_cost_estimate
	return []

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	
	#state ((A1),(A2),(B1),(B2)...)
	targets_temp = []
	passthroughs = set()
	state = {c:[] for c in 'ABCD'}
	graph = dict()
	for i in range(1,len(entries)-1):
		for j in range(1,len(entries[i])-1):
			if entries[i][j] in 'ABCD.':
				adjacency = []
				for di in [-1,1]:
					if entries[i+di][j] in 'ABCD.':
						adjacency.append((i+di,j))
					if entries[i][j] == '.' and entries[i+di][j] in 'ABCD':
						passthroughs.add((i,j))
				for dj in [-1,1]:
					if entries[i][j+dj] in 'ABCD.':
						adjacency.append((i,j+dj))
			graph[(i,j)] = adjacency
			if entries[i][j] in 'ABCD':
				state[entries[i][j]].append((i,j))
				targets_temp.append((i,j))

	state = tuple([pos for c in 'ABCD' for pos in state[c]])

	targets = {c:[] for c in 'ABCD'}
	for i,c in enumerate('ABCD'*2):
		targets[c].append(targets_temp[i])

	hallway = set()
	for n in graph.keys():
		if entries[n[0]][n[1]] == '.' and n not in passthroughs:
			hallway.add(n)

	#for k,v in graph.items():
	#	print(k,":",v)
	#print("State:",state)
	#print("Targets:",targets)
	#print("Passthroughs", passthroughs)
	#print("Hallway", hallway)

	G = nx.DiGraph()
	for n,e in graph.items():
		for t in e:
			G.add_edge(n,t)

	# A*
	cost, path = A_star(G, state, targets, hallway)
	#for state in path:
	#	print_state(entries, state)

	#neighbors = neighboring_states(G, state, targets, hallway)
	#for n in neighbors:
	#	print(n[0])
	#	print_state(entries, n[1])

	#queue = [state]
	#found = set(queue)
	#game_graph = nx.DiGraph()
	#while queue:
	#	curr = queue.pop()
	#	for cost, new_state in neighboring_states(G, curr, targets, hallway):
	#		if new_state not in found:
	#			found.add(new_state)
	#			queue.append(new_state)
	#		game_graph.add_edge(curr, new_state, weight=cost)
	#	print(len(found))

	return cost


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

