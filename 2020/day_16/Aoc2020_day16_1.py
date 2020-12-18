"""
Solution to Advent of Code 2020 day 16 part 1

Brute force
"""
import time
import sys

import re

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	fields,my,tickets = entries.split('\n\n')
	
	fields = [re.match(r'.* (\d+)-(\d+) or (\d+)-(\d+)',f).groups() for f in fields.splitlines()]

	ans = 0
	#print(fields)
	for tick in tickets.splitlines()[1:]:
		#print(tick)
		tick = [int(t) for t in tick.split(',')]
		for t in tick:
			#print(t,[int(f[0])<= t <=int(f[1]) or int(f[2])<= t <=int(f[3]) for f in fields])
			if not any([int(f[0])<= t <=int(f[1]) or int(f[2])<= t <=int(f[3]) for f in fields]):
				#print("in:",t)
				ans += t
	
	return ans

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
