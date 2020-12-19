"""
Solution to Advent of Code 2020 day 18 part 2

Shunting yard algorithm for RPN
"""
import time
import sys

import numpy as np
from scipy import ndimage

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	num = 0
	val_stack = []
	op_stack = []
	res = 0
	for line in entries:
		for c in line:
			if not c.isdigit() and num>0:
				val_stack.append(num)
				num = 0
			if c == ' ':
				continue
			elif c.isdigit():
				num = num * 10 + int(c)
			elif c == '*' or c == '+':
				while op_stack and op_stack[-1] != '(':
					val_stack.append(op_stack.pop())
				op_stack.append(c)
			elif c == '(':
				op_stack.append('(')
			elif c == ')':
				while op_stack[-1] != '(':
					val_stack.append(op_stack.pop())
				op_stack.pop()
		if num>0:
			val_stack.append(num)
			num = 0
		while op_stack:
			val_stack.append(op_stack.pop())
		#print(line, val_stack, op_stack)
		val_stack = val_stack[::-1]
		#print()
		t_stack = []
		while val_stack:
			tok = val_stack.pop()
			#print(tok, t_stack, val_stack)
			if tok == '*':
				x = t_stack.pop()
				y = t_stack.pop()
				t_stack.append(x*y)
			elif tok == '+':
				x = t_stack.pop()
				y = t_stack.pop()
				t_stack.append(x+y)
			else:
				t_stack.append(tok)
		#print(t_stack)
		res += t_stack.pop()

	return res

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
