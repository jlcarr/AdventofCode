"""
Solution to Advent of Code 2022 day 5 part 1

Solved by directly simulating the stack moving, popping one element at a time. Mostly was tricky parsing the data, did so by counting spacing between chars.
"""
import time
import sys

# tools
import re

import numpy as np
import scipy.ndimage

from collections import Counter
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	#entries = entries.strip()

	# Parsing
	stacks_parse, moves = entries.split('\n\n')
	
	# stacks
	stacks_parse = stacks_parse.splitlines()
	n = (len(stacks_parse[-1])+1)//4
	stacks = []
	for i in range(n):
		stacks.append([])
	#print(stacks_parse)
	for line in stacks_parse[:-1]:
		#print(line)
		i_stack = 0
		i = 1
		while i < len(line):
			if line[i] != ' ':
				stacks[i_stack].append(line[i])
			i += 4
			i_stack += 1
	stacks = [stack[::-1] for stack in stacks]
	print(stacks)
			
	# moves
	moves = moves.splitlines()
	for move in moves:
		move = move.split(' ')
		m_num = int(move[1])
		m_from = int(move[3])
		m_to = int(move[5])
		for i in range(m_num):
			#print(m_to, m_from)
			stacks[m_to-1].append(stacks[m_from-1].pop())
			

	return ''.join([stack[-1] for stack in stacks])

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

