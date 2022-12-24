"""
Solution to Advent of Code 2022 day 24 part 1

Used a list of keep track of blizzard positions and orientations and updated with modular arithmetic. The paths are independently cyclic, so just find the common multiple which was relatively low, and run through all board configurations once. Construct the graph of positions and round keys, with the final exit as a special position without round, then find the shortest path with NetworkX.
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

import math

import networkx as nx

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#entries = [re.findall(r'(\d+)',e)[0] for e in entries]
	entries = np.array(entries)
	entries = entries[1:-1,1:-1]
	#for row in entries:
	#	print(''.join(row))
		
	blizz_dirs = []
	blizz_pos = []
	m,n = entries.shape
	for i in range(m):
		for j in range(n):
			if entries[i,j] != '.':
				blizz_pos.append((i,j))
			if entries[i,j] == '>':
				blizz_dirs.append((0,1))
			elif entries[i,j] == '<':
				blizz_dirs.append((0,-1))
			elif entries[i,j] == 'v':
				blizz_dirs.append((1,0))
			elif entries[i,j] == '^':
				blizz_dirs.append((-1,0))
	#print(blizz_pos)
	#print(blizz_dirs)
	#print('shape', m,n)
	spaces = (entries=='.').sum()
	#print('space', spaces)
	
	def print_blizz(blizz_pos):
		board = np.array([['.']*m]*n)
		for i_blizz in range(len(blizz_pos)):
			pos = blizz_pos[i_blizz]
			if board[pos] not in '.><^v':
				board[pos] = str(1+int(board[pos]))
			if board[pos] in '><^v':
				board[pos] = str(2)
			else:
				if blizz_dirs[i_blizz] == (0,1):
					board[pos] = '>'
				elif blizz_dirs[i_blizz] == (0,-1):
					board[pos] = '<'
				elif blizz_dirs[i_blizz] == (1,0):
					board[pos] = 'v'
				elif blizz_dirs[i_blizz] == (-1,0):
					board[pos] = '^'
		for row in board:
			print(''.join(row))
	
	def update(blizz_pos):
		for i_blizz in range(len(blizz_pos)):
			blizz_pos[i_blizz] = ((blizz_pos[i_blizz][0] + blizz_dirs[i_blizz][0]) % m,
				(blizz_pos[i_blizz][1] + blizz_dirs[i_blizz][1]) % n)
			
	#update(blizz_pos)
	#update(blizz_pos)
	#update(blizz_pos)
	#update(blizz_pos)
	#print_blizz(blizz_pos)
	
	rounds = math.lcm(m,n)
	#print('rounds', rounds)
	#print('tot', rounds * spaces)

	blizz_pos_set = set(blizz_pos)
	free_pos = set([(i,j) for i in range(m) for j in range(n) if (i,j) not in blizz_pos_set] + [(-1,0), (m,n-1)])
	# Solving
	G = nx.DiGraph()
	for r in range(rounds):
		# update
		update(blizz_pos)
		blizz_pos_set = set(blizz_pos)
		#find connections from prev
		new_free_pos = set()
		for pos in free_pos:
			if pos not in blizz_pos_set:
				G.add_edge((r, *pos), ((r+1)%rounds, *pos))
				new_free_pos.add(pos)
			for k in [-1,1]:
				if 0<=pos[0]+k<m and 0<=pos[1]<n and (pos[0]+k, pos[1]) not in blizz_pos_set:
					G.add_edge((r, *pos), ((r+1)%rounds, pos[0]+k, pos[1]))
					new_free_pos.add((pos[0]+k, pos[1]))
				if 0<=pos[0]<m and 0<=pos[1]+k<n and (pos[0], pos[1]+k) not in blizz_pos_set:
					G.add_edge((r, *pos), ((r+1)%rounds, pos[0], pos[1]+k))
					new_free_pos.add((pos[0], pos[1]+k))
			if pos == (m-1,n-1): # end
				G.add_edge((r, *pos), (m,n-1))
		free_pos = new_free_pos
	#print(G.nodes())

	#print(nx.shortest_path(G, (0,-1,0), (m,n-1)))
	return nx.shortest_path_length(G, (0,-1,0), (m,n-1))

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

