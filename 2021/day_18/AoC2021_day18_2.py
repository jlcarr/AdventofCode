"""
Solution to Advent of Code 2021 day 18 part 2

Simply brute-force checked all pairs.
I don't think there's a more efficient way.
"""
import time
import sys

import re
import numpy as np
import math


def parse_tokens(entries):
	entries = list(entries)
	result = []
	for token in  entries:
		if token in '[,]':
			result.append(token)
		else:
			result.append(int(token))
	return result

def reduce_tokens(entries):
	changed = True
	while changed:
		#print("step:", ''.join(map(str,entries)))
		changed = False
		stack_count = 0
		for cursor in range(len(entries)):
			token = entries[cursor]
			if token == ',':
				continue
			elif token == '[':
				stack_count += 1
				if stack_count > 4:
					#print('explode')
					# explode
					left_val = entries[cursor+1]
					new_cursor = cursor -1
					while new_cursor >= 0:
						if isinstance(entries[new_cursor], int):
							entries[new_cursor] += left_val
							break
						new_cursor -= 1
					right_val = entries[cursor+3]
					new_cursor = cursor +5
					while new_cursor < len(entries):
						if isinstance(entries[new_cursor], int):
							entries[new_cursor] += right_val
							break
						new_cursor += 1
					entries = entries[:cursor] + [0] + entries[cursor+5:]
					changed = True
					break
			elif token == ']':
				stack_count -= 1
		if changed:
			continue
		stack_count = 0
		for cursor in range(len(entries)):
			token = entries[cursor]
			if token == ',':
				continue
			elif token == '[':
				stack_count += 1
			elif token == ']':
				stack_count -= 1
			elif token >= 10:
				# split
				#print('split', token, int(math.floor(token/2)), int(math.ceil(token/2)))
				entries = entries[:cursor] + ['[', int(math.floor(token/2)), ',', int(math.ceil(token/2)), ']'] + entries[cursor+1:]
				changed = True
				break
	return entries

def magnitude(tree):
	if isinstance(tree, int):
		return tree
	return 3*magnitude(tree[0]) + 2*magnitude(tree[1])

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()

	sol = 0
	for e1 in entries:
		for e2 in entries:
			curr = '[' + e1 + ',' + e2 + ']'
			curr = parse_tokens(curr)
			curr = reduce_tokens(curr)
			curr = ''.join(map(str,curr))
			mag = magnitude(eval(curr))
			#print(curr)
			if mag > sol:
				sol = mag
			#break

	#print(curr)

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

