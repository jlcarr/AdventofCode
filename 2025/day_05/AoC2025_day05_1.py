"""
Solution to Advent of Code 2025 day 5 part 1

Solved by sorting the ranges to run through them, and the ranges in inverse order to make a stack, which we can pop from while they are below the currently considered ranges upper bound, counting them if they are within the range. The sort guarantees everything works.
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

	ingredients = ingredients.splitlines()
	ingredients = [int(i) for i in ingredients]
	#print(ingredients)

	# Solving
	fresh.sort()
	ingredients.sort(reverse=True)

	#print(fresh)
	#print(ingredients)
	
	sol = 0
	for l,u in fresh:
		#print(l,u)
		while ingredients and ingredients[-1] < l:
			ingredients.pop()
		while ingredients and ingredients[-1] <= u:
			#print(ingredients[-1])
			ingredients.pop()
			sol += 1
		if not ingredients:
			break
		
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

