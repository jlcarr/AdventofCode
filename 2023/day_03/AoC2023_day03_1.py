"""
Solution to Advent of Code 2023 day 3 part 1

Solved by scanning by iterating over rows then cols, building up numbers found, and for each position scanning for adjacent symbols, then adding once end of number is found.
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
	entries = entries.splitlines()
	#print(entries)
	
	rows, cols = len(entries), len(entries[0])
	sol = 0
	for i in range(rows):
		num = ''
		partnum = False
		for j in range(cols):
			if entries[i][j] in '0123456789':
				num += entries[i][j]
				for ix in [i-1,i,i+1]:
					for jx in [j-1,j,j+1]:
						if (0 <= ix < rows) and (0 <= jx < cols) and (entries[ix][jx] not in '.0123456789'):
							partnum = True
			else:
				if partnum and num:
					#print(num)
					sol += int(num)
				partnum = False
				num = ''
		if partnum and num:
			sol += int(num)
		partnum = False
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

