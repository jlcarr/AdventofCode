"""
Solution to Advent of Code 2024 day 24 part 1

Solved using functools cache to construct a recursive function looking upstream from each wire's values through the inputs of its logic gate, which are accessed quickly via a dictionary.
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
	defaults, connections = entries.split('\n\n')
	
	defaults = dict([v.split(': ') for v in defaults.splitlines()])
	
	connections = [v.split(' -> ') for v in connections.splitlines()]
	connections = [(ex.split(' '),out) for ex,out in connections]
	
	#print(defaults)
	#print(connections)
	
	# Setup
	invconnections = {out: ins for ins,out in connections}
	#print(invconnections)

	allnodes = set(defaults.keys()) | set(invconnections.keys()) | set([l for (l,op,r),out in connections]) | set([r for (l,op,r),out in connections])
	#print(allnodes)
	
	zs = sorted([node for node in allnodes if node.startswith('z')])
	#print(zs)
	
	# Solving
	@cache
	def rec(v):
		if v in invconnections:
			l,op,r = invconnections[v]
			if op == 'AND':
				return rec(l) and rec(r)
			if op == 'OR':
				return rec(l) or rec(r)
			if op == 'XOR':
				return rec(l) ^ rec(r)
			print('INVALID')
			return None
		return defaults[v] == '1'
	
	return sum(rec(z) * 2**i for i,z in enumerate(zs))


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

