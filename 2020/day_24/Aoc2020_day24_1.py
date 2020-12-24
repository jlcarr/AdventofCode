"""
Solution to Advent of Code 2020 day 24 part 1

Hexagonal coordinate system. Used a E-W and NE-SW system
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	#print(entries)

	found_set = set()
	for tile in entries:
		#tile = 'nwwswee' # TEST
		x,y = 0,0
		#print(tile)
		while len(tile) > 0:
			if tile[0] == 'n':
				y += 1
				if tile[1] == 'w':
					x -= 1
				tile = tile[2:]
			elif tile[0] == 's':
				y -= 1
				if tile[1] == 'e':
					x += 1
				tile = tile[2:]
			elif tile[0] == 'e':
				x += 1
				tile = tile[1:]
			elif tile[0] == 'w':
				x -= 1
				tile = tile[1:]
			#print(x,y, tile)
		#print(x,y)
		if (x,y) in found_set:
			found_set.remove((x,y))
		else:
			found_set.add((x,y))
	return len(found_set)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
