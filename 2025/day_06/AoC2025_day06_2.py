"""
Solution to Advent of Code 2025 day 6 part 2

Solved by keeping the whole table and iterating down the column, accumulating operands, and performing the operations when new ops are found. Careful of off-by-1 errors!
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage
import math

from collections import Counter, deque
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	#entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	ops = entries[-1]
	entries = entries[:-1]
	#entries = [list(map(int,e.split())) for e in entries[:-1]]
	#entries = np.array(entries)
	#print(ops)
	#print(entries)

	#print(len(ops))
	#print(list(map(len,entries)))

	ops += 'X'

	# Solving
	op = ops[0]
	vals = []
	cvals = []
	for i,new_op in enumerate(ops):
		if new_op != ' ' and vals:
			#print(op, vals, sum(vals) if op == '+' else math.prod(vals))
			if op == '+':
				cvals.append(sum(vals))
			elif op == '*':
				cvals.append(math.prod(vals))
			if new_op == 'X':
				break
			vals = []
			op = new_op
		empty = True
		acc = 0
		for row in entries:
			if row[i] == ' ':
				continue
			empty = False
			acc = acc * 10 + int(row[i])
		if not empty:
			vals.append(acc)
	#print(cvals)
	return sum(cvals)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

