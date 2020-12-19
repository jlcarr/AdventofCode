"""
Solution to Advent of Code 2020 day 12 part 1

Brute force
"""
import time
import sys

import re
import math

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = [re.match(r'([A-Z]+)([0-9]+)',e).groups() for e in entries]
	#print(entries)
	
	angle = 0
	x = 0
	y = 0
	for i,v in entries:
		if i == 'N':
			y += int(v)
		if i == 'S':
			y -= int(v)
		if i == 'E':
			x += int(v)
		if i == 'W':
			x -= int(v)
		if i == 'L':
			angle += int(v)
		if i == 'R':
			angle -= int(v)
		if i == 'F':
			x += int(v)*math.cos(angle*math.pi/180)
			y += int(v)*math.sin(angle*math.pi/180)
		#print(x,y,angle)
	return abs(round(x))+abs(round(y))
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
