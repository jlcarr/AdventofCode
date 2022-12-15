"""
Visualization of Advent of Code 2022 day 14 part 1
"""
import time
import sys

# tools
import re
import json

import numpy as np
import scipy.ndimage
from PIL import Image

from collections import Counter, deque
from functools import cache


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [[[int(x) for x in p.split(',')] for p in e.split(' -> ')] for e in entries]
	xmin = min([p[0] for e in entries for p in e])
	xmax = max([p[0] for e in entries for p in e])
	ymin = min([p[1] for e in entries for p in e])
	ymin = 0
	ymax = max([p[1] for e in entries for p in e])
	grid = np.zeros((ymax+1,xmax+1), dtype=int)
	for e in entries:
		for p1,p2 in zip(e[:-1],e[1:]):
			if p1[0] == p2[0]:
				s, e = min(p1[1],p2[1]), max(p1[1],p2[1])
				grid[s:e+1, p1[0]] = 1
			elif p1[1] == p2[1]:
				s, e = min(p1[0],p2[0]), max(p1[0],p2[0])
				grid[p1[1], s:e+1] = 1
			#print(p1[0],p2[0]+1,p1[1],p2[1]+1)
		
	#print(grid)
	#img = grid.astype('uint8')*255
	#img[0,500] = 255//2
	#Image.fromarray(img).save('test.png')
	imgs = []

	sol = 0
	while True:
		curr = [0, 500]
		while True:
			if curr[0]+1 >= ymax:
				imgs[0].save('test.gif', save_all=True, append_images=imgs[1:], duration=len(imgs)//16)
				return sol
			if grid[curr[0]+1, curr[1]] == 0:
				curr[0] += 1
				continue
			if curr[0]-1 < 0:
				imgs[0].save('test.gif', save_all=True, append_images=imgs[1:], duration=len(imgs)//16)
				return sol
			if grid[curr[0]+1, curr[1]-1] == 0:
				curr[0] += 1
				curr[1] -= 1
				continue
			if curr[1]+1 >= xmax:
				imgs[0].save('test.gif', save_all=True, append_images=imgs[1:], duration=len(imgs)//16)
				return sol
			if grid[curr[0]+1, curr[1]+1] == 0:
				curr[0] += 1
				curr[1] += 1
				continue
			grid[tuple(curr)] = 2
			sol += 1
			break
		img = np.zeros((ymax-ymin+1, xmax-xmin+1, 3), dtype='uint8')
		img += np.repeat(grid[ymin:ymax+1, xmin:xmax+1, np.newaxis] == 1, 3, axis=2).astype('uint8') * 255
		img[:,:,0:1+1] += np.repeat(grid[ymin:ymax+1, xmin:xmax+1, np.newaxis] == 2, 2, axis=2).astype('uint8') * 255
		if ymin <= curr[0] < ymax and xmin <= curr[1] < xmax:
			img[curr[0]-ymin, curr[1]-xmin, 0] = 255
		img[0,500-xmin,2] = 255
		imgs.append(Image.fromarray(img))
	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

