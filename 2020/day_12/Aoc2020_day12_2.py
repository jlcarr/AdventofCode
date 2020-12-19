"""
Solution to Advent of Code 2020 day 12 part 2

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
	
	
	x = 0
	y = 0

	x_w = 10
	y_w = 1
	for i,v in entries:
		if i == 'N':
			y_w += int(v)
		if i == 'S':
			y_w -= int(v)
		if i == 'E':
			x_w += int(v)
		if i == 'W':
			x_w -= int(v)
		if i == 'L':
			a = int(v) * math.pi/180.0
			x_temp = x_w *math.cos(a) - y_w*math.sin(a)
			y_temp = x_w*math.sin(a) + y_w*math.cos(a)
			x_w = x_temp
			y_w = y_temp
		if i == 'R':
			a = -int(v)* math.pi/180.0
			#print(a,v)
			x_temp = x_w *math.cos(a) - y_w *math.sin(a)
			y_temp = x_w *math.sin(a) + y_w *math.cos(a)
			x_w = x_temp
			y_w = y_temp
		if i == 'F':
			x +=x_w * int(v)
			y +=y_w * int(v)
		#print(x,y,x_w,y_w)
	return abs(round(x))+abs(round(y))
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
