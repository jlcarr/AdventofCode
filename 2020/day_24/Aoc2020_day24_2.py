"""
Solution to Advent of Code 2020 day 24 part 2

Use set union, and set difference with a neighbors search
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
	
	neighbor_pos = [(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
	black_set = found_set
	for t in range(100):
		no_longer_black = set()
		new_black = set()
		for tile in black_set:
			x,y = tile
			# self black to white?
			neighbor = sum([1 for x_i,y_i in neighbor_pos if (x+x_i,y+y_i) in black_set])
			if neighbor== 0 or neighbor>2:
				no_longer_black.add(tile)
			#neighbors while to black?
			for x_i,y_i in neighbor_pos:
				if (x+x_i,y+y_i) not in black_set:
					neighbor = sum([1 for x_j,y_j in neighbor_pos if (x+x_i+x_j,y+y_i+y_j) in black_set])
					if neighbor == 2:
						new_black.add((x+x_i,y+y_i))
		black_set -= no_longer_black
		black_set |= new_black
	return len(black_set)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
