"""
Solution to Advent of Code 2021 day 6 part 2

Dynamic programming with memoization, 5D statespace `(10*10*21*21*2)`. Construct all possible results of a turn and follow their game trees.
"""
import time
import sys

import re
import numpy as np
from functools import lru_cache

@lru_cache(maxsize=None)
def gamestate_count(pos1,pos2,score1,score2, turn):
	if score1 >= 21:
		return [1,0]
	if score2 >= 21:
		return [0,1]
	ans = [0,0]
	for roll1 in range(3):
		for roll2 in range(3):
			for roll3 in range(3):
				if turn==0:
					new_pos1 = (pos1 + roll1+1 + roll2+1 + roll3+1)%10
					new_score1 = score1 + new_pos1+1
					new_turn = (turn+1)%2
					new_ans = gamestate_count(new_pos1,pos2,new_score1,score2, new_turn)
					ans = [i+j for i,j in zip(ans,new_ans)]
				else:
					new_pos2 = (pos2 + roll1+1 + roll2+1 + roll3+1)%10
					new_score2 = score2 + new_pos2+1
					new_turn = (turn+1)%2
					new_ans = gamestate_count(pos1,new_pos2,score1,new_score2, new_turn)
					ans = [i+j for i,j in zip(ans,new_ans)]
	return ans

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [re.findall(r'Player \d starting position: (\d+)',e)[0] for e in entries]
	pos = [int(e)-1 for e in entries]
	#print(pos)

	wins = gamestate_count(pos[0],pos[1],0,0, 0)

	#print(wins)

	return max(wins)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

