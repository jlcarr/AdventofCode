"""
Solution to Advent of Code 2020 day 8 part 2

Solved by brute force, quadratic time
Try all different steps to swap
Linear time is possible by constructing the graph of instruction (will be disconnected)
1 path will go from the start into a loop
Either
a) Another will be a tree where children direct to parents (could be linear) with the root jmp-ing to the end
b) One of the nop instructions in the start path can be swapped to a jmp that will terminate
linearly search through the first path for a nop that when swapped to a jmp will either
jump to the ending-tree (scenario a)
or go straight to the end (scenario b)
also look for a jmp whose instruction below is in the ending-tree (swapping to a nop will be scenario a)
"""
import time
import sys

import re

def valid_entry(p):
	count = set()
	#print(f"\nStart: {p}")
	for v in p:
		try:
			f,val = v.split(':')
		except:
			continue
		if f == 'byr':
			if len(val) == 4 and 1920 <= int(val) <= 2002:
				count.add(f)
		elif f == 'hcl':
			if val.startswith('#') and len(re.findall(r'[0-9a-f]',val)) == len(val)-1:
				count.add(f)
		elif f == 'ecl':
			if val in {'amb','blu', 'brn', 'gry', 'grn', 'hzl', 'oth'}:
				count.add(f)
		elif f == 'pid':
			if bool(re.match(r'^[0-9]+$',val)) and len(val)==9:
				count.add(f)
	#print(count)
	return all(c in count for c in {'byr','iyr','eyr','eyr','hgt','hcl','ecl','pid'})

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()

	swap = 0
	while True:
		insset = set()
		i = 0
		acc = 0
		while i not in insset and i < len(entries):
			insset.add(i)
			ins, v = entries[i].split(' ')
			if len(insset)-1 == swap:
				if ins == 'jmp':
					ins = 'nop'
				elif ins == 'nop':
					ins = 'jmp'
			
			if ins == 'jmp':
				i += int(v)
				continue
			elif ins == 'acc':
				acc += int(v)
			i += 1
		if i == len(entries):
			return acc
		swap += 1
	
	# Brute force loop
	valid = [p for p in entries if valid_entry(p)]
	return len(valid)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
