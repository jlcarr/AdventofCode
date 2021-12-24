"""
Solution to Advent of Code 2021 day 24 part 2

I found that the output wasn't particularly sensitive to input: random flip sets of digits, keeping records of the max found, hoping to break out of local maxima into a global maxima.
More elegant solution could be to use an actual SAT-solver like Z3
Also considered genetic algorithms
Also I would assume simulated annealing to give temperatures to the digits would be more effective.
"""
import time
import sys

import re
import numpy as np
import random

def ALU(prog, inp):
	vars = {c:0 for c in 'xyzq'}
	for line in prog:
		if len(line) > 2:
			b = line[2]
			if b in vars:
				b = vars[b]
			else:
				b = int(b)
		if line[0] == 'inp':
			vars[line[1]] = int(inp.pop())
		elif line[0] == 'add':
			vars[line[1]] = vars[line[1]] + b
		elif line[0] == 'mul':
			vars[line[1]] = vars[line[1]] * b
		elif line[0] == 'div':
			if b == 0:
				return None
			vars[line[1]] = vars[line[1]] // b
		elif line[0] == 'mod':
			if b <= 0 or vars[line[1]] < 0:
				return None
			vars[line[1]] = vars[line[1]] % b
		elif line[0] == 'eql':
			vars[line[1]] = int(vars[line[1]] == b)
	return vars

def create_tree(prog):
	# This doesn't seem to be working right?
	op_map = {'add':'+', 'mul':'*', 'div':'/', 'mod':'%', 'eql':'='}
	input_counter = 0
	vars = {c:0 for c in 'xyzq'}
	for line in prog:
		if len(line) > 2:
			b = line[2]
			if b in vars:
				b = vars[b]
			else:
				b = int(b)
		if line[0] == 'inp':
			vars[line[1]] = "inp"+str(input_counter)
			input_counter += 1
		else:
			vars[line[1]] = (op_map[line[0]], vars[line[1]], b)

	return vars

def print_tree(tree):
	# unimplemneted
	pass

def execute_tree(tree, inp):
	# Also unimplemented
	if isinstance(tree, int):
		return tree
	elif isinstance(tree, str):
		return int(inp[int(tree[3:])])
	elif isinstance(tree, max):
		pass

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [e.split(' ') for e in entries]
	#print(entries)
	
	# test input
	inp = '13579246899999'
	inp = list(inp)[::-1]

	#inp = '92939959792499'
	#inp = list(inp)
	
	result = ALU(entries, inp)
	print(result)

	# Initiate
	inp = list('9'*14)
	#inp = list('92939959792499')
	#inp = list('89429795993928')[::-1]
	val =  ALU(entries, inp[:])

	# pass through a few times deterministically searching single digit flips
	for k in range(4):
		for i in range(14):
			for j in range(1,10):
				new_inp = inp[:]
				new_inp[i] = str(j)
				new_val = ALU(entries, new_inp[:])
				if new_val is not None and np.abs(new_val['z']) <= np.abs(val['z']):
					if np.abs(val['z']) > 0 or inp[::-1] < new_inp[::-1]:
						val = new_val
						inp = new_inp

	# Try flipping random sets of digits
	for k in range(1000000):
		new_inp = inp[:]
		for r in range(random.randint(1,14)):
			i = random.randint(0,13)
			new_inp[i] = str(random.randint(1,9))
		new_val = ALU(entries, new_inp[:])
		# First try to minimize Z to get a solution, then try to maximize it
		if new_val is not None and np.abs(new_val['z']) <= np.abs(val['z']):
			if np.abs(val['z']) > 0 or inp[::-1] <= new_inp[::-1]:
				val = new_val
				inp = new_inp
	print(val)
	#print(''.join(inp))
	print(''.join(inp[::-1]))

	sol = None
	if val['z'] == 0:
		sol = int(''.join(inp[::-1]))

	# Pure brute force?
	#val = int('9'*14)
	#while True:
	#	rval = ALU(entries, list(str(val)))
	#	print(val, rval['z'])
	#	if rval['z'] == 0:
	#		break
	#	val -=1


	#result = create_tree(entries)
	#print(result)
	#print(execute_tree('inp0', ['7']))

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

