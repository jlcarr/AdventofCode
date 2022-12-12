"""
Solution to Advent of Code 2022 day 11 part 2

Same as part 1, but the worry to explode taking up a lot of memory and computational time: we only need the divisibility as a test, and that won't change if we work with the modulus of a number that is divisible by all divisibility tests.
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
	monkies = []
	for monkey in entries.split('\n\n'):
		monkey = monkey.splitlines()
		op_val = monkey[2].split(' ')[-1]
		monkies.append({
			'items': [int(item) for item in monkey[1].split(':')[1].strip().split(', ')],
			'op': monkey[2].split(' ')[-2],
			'op_val': op_val if op_val == 'old' else int(op_val),
			'div': int(monkey[3].split(' ')[-1]),
			'true_val': int(monkey[4].split(' ')[-1]),
			'false_val': int(monkey[5].split(' ')[-1])
		})

	#print(json.dumps(monkies, indent=4))

	mod_val = 1
	for m in monkies:
		m['items'] = deque(m['items'])
		if mod_val % m['div'] != 0:
			mod_val *= m['div']

	# Solving
	inspections = [0] * len(monkies)
	for i in range(10000):
		for j,m in enumerate(monkies):
			while m['items']:
				item = m['items'].popleft()
				inspections[j] += 1
				if m['op'] == '+':
					new_val = item + (item if m['op_val'] == 'old' else m['op_val'])
				elif m['op'] == '*':
					new_val = item * (item if m['op_val'] == 'old' else m['op_val'])
				#new_val = new_val//3
				new_val = new_val % mod_val
				if new_val % m['div'] == 0:
					monkies[m['true_val']]['items'].append(new_val)
				else:
					monkies[m['false_val']]['items'].append(new_val)
		#if i % 100 == 0:
		#	print(i)
	monkey_business = sorted(inspections)
	return monkey_business[-1] * monkey_business[-2]

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

