"""
Solution to Advent of Code 2021 day 12 part 1

Solved using depth-first search
"""
import time
import sys

import re
import numpy as np
import copy


def DFS(adj_map, path=['start'], visited=set(['start'])):
	all_paths = []
	for target in adj_map[path[-1]]:
		if target == 'end':
			all_paths += [path]
		elif target not in visited:
			new_path = copy.deepcopy(path)
			new_path.append(target)
			new_visited = copy.deepcopy(visited)
			if not re.match(r'[A-Z]+', target):
				new_visited.add(target)
			all_paths += DFS(adj_map, path=new_path, visited=new_visited)
	return all_paths


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	# Parsing
	entries = entries.splitlines()
	entries = [re.findall(r'(\w+)-(\w+)',e)[0] for e in entries]

	adj_map = {}
	for s,e in entries:
		if s not in adj_map:
			adj_map[s] = set()
		adj_map[s].add(e)
		if e not in adj_map:
			adj_map[e] = set()
		adj_map[e].add(s)
	#print(adj_map)


	all_paths = DFS(adj_map)
	#for p in all_paths:
	#	print(p)

	return len(all_paths)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

