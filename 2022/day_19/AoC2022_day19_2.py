"""
Solution to Advent of Code 2022 day 19 part 2

I ended up finding that the fastest way for me to solve this one was to just wait the extra time for the longer depth search to run. Optimizations from part 1 apply to part 2 as well.
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


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	test = False
	if test:
		entries = entries.split('\n\n')
		entries = '\n'.join([' '.join([j.strip() for j in e.splitlines()]) for e in entries])
	entries = entries.splitlines()

	entries = [re.findall(r'Blueprint (\d+): Each ore robot costs (\d+) ore. Each clay robot costs (\d+) ore. Each obsidian robot costs (\d+) ore and (\d+) clay. Each geode robot costs (\d+) ore and (\d+) obsidian.',e)[0] for e in entries]
	entries = [tuple([int(j) for j in e]) for e in entries]
	#entries = [{'num':e[0], 'ore': e[1], 'clay': e[2], 'obsidian': (e[3], e[4]), 'geode': (e[5], e[6])} for e in entries]
	#print(entries)

	# Solving
	
	def update_ores(resources, robots):
		for i,r in enumerate(robots):
			resources[i] += r
	def unupdate_ores(resources, robots):
		for i,r in enumerate(robots):
			resources[i] -= r
	
	# dont need geoges: just score up immediately
	@cache
	def dp(blueprint, resources, robots, t_rem):
		#print(resources, robots, t_rem)
		if t_rem == 1:
			return 0, []
		resources, robots = list(resources), list(robots)
		
		# first try to build an geode
		result = 0
		path = []
		
		# none
		# geode bots
		if resources[0] >= blueprint[5] and resources[2] >= blueprint[6]:
			update_ores(resources, robots)
			resources[0] -= blueprint[5]
			resources[2] -= blueprint[6]
			sub_score, subpath = dp(blueprint, tuple(resources), tuple(robots), t_rem-1)
			sub_score += t_rem-1
			result = max(result, sub_score)
			return result, [] #['geode'] + subpath
		# none
		if True or resources[0] < max([blueprint[1], blueprint[2], blueprint[3], blueprint[5]]):
			update_ores(resources, robots)
			result, path = dp(blueprint, tuple(resources), tuple(robots), t_rem-1)
			unupdate_ores(resources, robots)
			path = []#['none'] + path
		# ore bots 0
		if resources[0] >= blueprint[1] \
			and robots[0] < max([blueprint[1], blueprint[2], blueprint[3], blueprint[5]]):
			update_ores(resources, robots)
			resources[0] -= blueprint[1]
			robots[0] += 1
			sub_score, subpath = dp(blueprint, tuple(resources), tuple(robots), t_rem-1)
			if sub_score > result:
				result = max(result, sub_score)
				path = [] #['ore'] + subpath
			resources[0] += blueprint[1]
			robots[0] -= 1
			unupdate_ores(resources, robots)
		# clay bots 1
		if resources[0] >= blueprint[2] \
			and robots[1] < blueprint[4]:
			update_ores(resources, robots)
			resources[0] -= blueprint[2]
			robots[1] += 1
			sub_score, subpath = dp(blueprint, tuple(resources), tuple(robots), t_rem-1)
			if sub_score > result:
				result = max(result, sub_score)
				path = [] #['clay'] + subpath
			resources[0] += blueprint[2]
			robots[1] -= 1
			unupdate_ores(resources, robots)
		# obsidian bots 2
		if resources[0] >= blueprint[3] and resources[1] >= blueprint[4] \
			and robots[2] < blueprint[6]:
			update_ores(resources, robots)
			resources[0] -= blueprint[3]
			resources[1] -= blueprint[4]
			robots[2] += 1
			sub_score, subpath = dp(blueprint, tuple(resources), tuple(robots), t_rem-1)
			if sub_score > result:
				result = max(result, sub_score)
				path = [] #['obsidian'] + subpath
			resources[0] += blueprint[3]
			resources[1] += blueprint[4]
			robots[2] -= 1
			unupdate_ores(resources, robots)
		return result, path

	sol = 1
	for i,n in enumerate(entries):
		if i == 3:
			break
		#print('\nblueprint', {'num':n[0], 'ore': n[1], 'clay': n[2], 'obsidian': (n[3], n[4]), 'geode': (n[5], n[6])})
		blueprint_sol = dp(n, (0,0,0), (1,0,0), 32)
		#print(blueprint_sol)
		sol *= blueprint_sol[0]

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

