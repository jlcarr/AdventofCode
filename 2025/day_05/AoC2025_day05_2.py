"""
Solution to Advent of Code 2025 day 5 part 2

Solved with a sort again, this time keeping track of the last considered upper bound, so we have the cases of the next range being engulfed, extending the range, or being completely outside it.
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage

from collections import Counter, deque
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	fresh, ingredients = entries.split("\n\n")

	fresh = fresh.splitlines()
	fresh = [re.findall(r'(\d+)-(\d+)',e)[0] for e in fresh]
	fresh = [tuple(map(int,e)) for e in fresh]
	#print(fresh)

	#ingredients = ingredients.splitlines()
	#ingredients = [int(i) for i in ingredients]
	#print(ingredients)

	# Solving
	fresh.sort()
	#ingredients.sort(reverse=True)

	#print(fresh)
	#print(ingredients)
	
	l,u = fresh[0]
	sol = u-l+1
	for new_l,new_u in fresh:
		if new_u <= u: # complete overlap
			continue
		if new_l <= u: # some overlap
			l,u = u+1,new_u #remove overlap
		else: # no overlap
			l,u = new_l,new_u
		sol += u-l+1
		
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

