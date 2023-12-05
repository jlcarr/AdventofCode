"""
Solution to Advent of Code 2023 day 5 part 2

Solved by keeping track of ranges, and checking for range intersection, then cutting up the ranges as needed, and keeping the seeds in a stack in case they get cut into multiple ranges.
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
	entries = entries.split('\n\n')
	seeds = list(map(int, entries[0].split(': ')[1].split()))
	seeds = [(seeds[2*i], seeds[2*i+1]) for i in range(len(seeds)//2)]
	#print('seeds', seeds)
	#print('startsum', sum([s[1] for s in seeds]))
	
	entries = [e.splitlines()[1:] for e in entries[1:]]
	entries = [[list(map(int, rng.split())) for rng in e] for e in entries]
	entries = [sorted(e, key=lambda rng: rng[1]) for e in entries]
	#print('mappings', entries)

	for i,e in enumerate(entries):
		newseeds = []
		while seeds:
			s,l = seeds.pop()
			#print(s,l)
			newseeds.append((s,l))
			for rng in e:
				if (rng[1] < s+l) and (s < rng[1]+rng[2]):
					cuts = max(s, rng[1])
					cutl = min(s+l, rng[1]+rng[2]) - cuts
					
					newseeds[-1] = (cuts-rng[1] + rng[0], cutl)
					
					if s < cuts:
						seeds.append((s,cuts-s))
					if cuts+cutl < s+l:
						seeds.append((cuts+cutl,s+l - (cuts+cutl)))
					
					break
		seeds = newseeds
		#print(f'{i}:', seeds)
	#print('fin', seeds)
	#print('finsum', sum([s[1] for s in seeds]))
	return min([s[0] for s in seeds])


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

