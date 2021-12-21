"""
Solution to Advent of Code 2021 day 21 part 1

Direct simulation using modular arithmetic and accounting for off-by-one.
I wonder if a closed form solution is possible.
"""
import time
import sys

import re
import numpy as np

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [re.findall(r'Player \d starting position: (\d+)',e)[0] for e in entries]
	pos = [int(e)-1 for e in entries]
	#print(pos)

	scores = [0,0]
	die_val = 0
	turn = 0
	die_rolls = 0
	while max(scores) < 1000:
		pos[turn] = (pos[turn] + die_val+1)%10
		die_val = (die_val+1)%100
		pos[turn] = (pos[turn] + die_val+1)%10
		die_val = (die_val+1)%100
		pos[turn] = (pos[turn] + die_val+1)%10
		die_val = (die_val+1)%100
		scores[turn] += pos[turn]+1
		#print(turn, die_val, pos[turn], scores[turn])
		turn = (turn+1)%2
		die_rolls += 3

	#print(scores, die_rolls)
	return min(scores)*die_rolls

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

