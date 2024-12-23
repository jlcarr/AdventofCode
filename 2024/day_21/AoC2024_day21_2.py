"""
Solution to Advent of Code 2024 day 21 part 2

Solved using dynamic programming over pairs of instructions and robot outputting each. Essentially each pair of adjacent instruction that need to be output receives the same instructions from the next robot in depth. We can therefore setup the problem recursively and cache the costs (as well as the instructions themselves for debugging). The state space is too large for Dijkstra's.
"""
import time
import sys

# tools
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	#entries = [list(e) for e in entries]
	#print(entries)
	
	npad = [
		['7','8','9'],
		['4','5','6'],
		['1','2','3'],
		[' ','0','A'],
	]
	invnpad = {c:(i,j) for i,row in enumerate(npad) for j,c in enumerate(row)}
	dpad = [
		[' ','^','A'],
		['<','v','>'],
	]
	
	dmap = {
		'^': (-1,0),
		'v': (1,0),
		'<': (0,-1),
		'>': (0,1),
	}
	
	
	nr = 25
	dpad_instr = {
		'^': '<A',
		'v': '<vA',
		'<': 'v<<A',
		'>': 'vA',
	}
	dpad_instr = {
		'^^': 'A',
		'^v': 'vA',
		'^<': 'v<A',
		'^>': 'v>A',
		'^A': '>A',
		
		'v^': '^A',
		'vv': 'A',
		'v<': '<A',
		'v>': '>A',
		'vA': '^>A',

		'<^': '>^A',
		'<v': '>A',
		'<<': 'A',
		'<>': '>>A',
		'<A': '>>^A',

		'>^': '<^A',
		'>v': '<A',
		'><': '<<A',
		'>>': 'A',
		'>A': '^A',
		
		'A^': '<A',
		'Av': '<vA',
		'A<': 'v<<A',
		'A>': 'vA',
		'AA': 'A',
	}
	# wrong1: 320471787581532
	#
	
	#                          8
	#A       ^^        <       A
	#A   <   AA  v <   A >>  ^ A
	#Av<<A>>^AAv<A<A>>^AvAA^<A>A
	
	#                  0
	#          <       A
	#   v <<   A >>  ^ A
	# <vA<AA>>^AvAA<^A>A
	
	@cache
	def cost(pair, r):
		if r == 0:
			return 1, '' #pair[1]
		inst = 'A'+dpad_instr[pair]
		#print(pair,r, inst)
		result = 0
		tot_inst = []
		for c1,c2 in zip(inst[:-1],inst[1:]):
			#print(r,c1,c2)
			sub_result, sub_tot_inst = cost(c1+c2, r-1)
			result += sub_result
			tot_inst.append(sub_tot_inst)
		return result, ''.join(tot_inst)
	
	def cost_top(inst, rs):
		tot_inst = []
		result = 0
		for c1,c2 in zip(inst[:-1],inst[1:]):
			#print(c1,c2)
			sub_result, sub_tot_inst = cost(c1+c2, rs)
			result += sub_result
			tot_inst.append(sub_tot_inst)
		tot_inst = ''.join(tot_inst)
		return result, tot_inst
	
	#inst = "A^^<A"
	#inst = "A<A"
	#result, tot_inst = cost_top(inst, 2)
	#print(tot_inst)
	
	result = 0
	for code in entries:
		codecost = 0
		tempcode = 'A' + code
		presses = []
		for d1,d2 in zip(tempcode[:-1],tempcode[1:]):
			#print(d1,d2)
			di = invnpad[d2][0]-invnpad[d1][0]
			ud = ('v' if di > 0 else '^') * abs(di)
			dj = invnpad[d2][1]-invnpad[d1][1]
			lr = ('>' if dj > 0 else '<') * abs(dj)
			
			cost1, intr1 = cost_top('A'+ud+lr+'A', nr)
			cost2, intr2 = cost_top('A'+lr+ud+'A', nr)
			
			#print(ud+lr,cost1,lr+ud,cost2)
			
			# handle ' ' gap avoid
			if d1 in '0A' and d2 in '741':
				codecost += cost1
				presses.append(intr1)
			elif d1 in '741' and d2 in '0A':
				codecost += cost2
				presses.append(intr2)
			else:
				codecost += min(cost1,cost2)
				presses.append(intr1 if cost1 < cost2 else intr2)
		#print(codecost)
		#print(''.join(presses))
		result += codecost * int(code[:-1])
	return result
	
	
if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

