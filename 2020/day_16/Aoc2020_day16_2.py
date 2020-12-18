"""
Solution to Advent of Code 2020 day 16 part 2

Keeps a list of possibilities and cut it down by failed conditions
"""
import time
import sys

import re

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	fields,my,tickets = entries.split('\n\n')

	field_name = [f.split(':')[0] for f in fields.splitlines()]
	fields = [re.match(r'.* (\d+)-(\d+) or (\d+)-(\d+)',f).groups() for f in fields.splitlines()]

	ans = 0
	#print(fields)
	valids = []
	for tick in tickets.splitlines()[1:]:
		#print(tick)
		tick = [int(t) for t in tick.split(',')]
		inv = False
		for t in tick:
			#print(t,[int(f[0])<= t <=int(f[1]) or int(f[2])<= t <=int(f[3]) for f in fields])
			if not any([int(f[0])<= t <=int(f[1]) or int(f[2])<= t <=int(f[3]) for f in fields]):
				#print("in:",t)
				ans += t
				inv = True
		if not inv:
			valids.append(tick)
	#print(field_name)
	field_poss = dict()
	for i in range(len(valids[0])):
		field_poss[i] = set(field_name)
	#print(field_poss)

	for tick in valids:
		for i,t in enumerate(tick):
			for j,f in enumerate(fields):
				if not (int(f[0])<= t <=int(f[1]) or int(f[2])<= t <=int(f[3])):
					field_poss[i].remove(field_name[j])
	#print(field_poss)
	change = True
	while change:
		change = False
		for s in list(field_poss.values()):
			if len(s) == 1:
				v = next(iter(s))
				for k in list(field_poss.keys()):
					if len(field_poss[k]) > 1 and v in field_poss[k]:
						field_poss[k].remove(v)
						change = True
	#print(field_poss)

	ans = 1
	my = list(map(int,my.splitlines()[1].split(',')))
	#print(my)
	for k,v in field_poss.items():
		if 'departure' in next(iter(v)):
			ans *= my[k]


	return ans

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
