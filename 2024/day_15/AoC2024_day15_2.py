"""
Solution to Advent of Code 2024 day 15 part 2

Solved using a BFS search with a queue for the parts of boxes moved, and creating a stack of moves to be made should the move succeed, the ordering allows for moved box parts to move to their new position, and leave empty places behind them, possible filled by boxes behind them entering.
"""
import time
import sys

# tools
from collections import deque


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	grid, moves = entries.split('\n\n')
	grid = [list(l) for l in grid.splitlines()]
	gmap = {'#': '##', 'O': '[]', '.':'..', '@':'@.'}
	grid = [[x for c in row for x in gmap[c]] for row in grid]
	moves = moves.replace('\n','')
	#print('\n'.join([''.join(r) for r in grid]))
	#print(moves)
	pos = [(i,j) for i,row in enumerate(grid) for j,c in enumerate(row) if c == '@'][0]
	#print(pos)
	
	mmap = {'>':(0,1), '<':(0,-1), '^':(-1,0), 'v':(1,0)}
	for m in moves:
		#print('move', m)
		di,dj = mmap[m]
		i,j = pos
		if grid[i+di][j+dj] == '.':
			grid[i+di][j+dj] = '@'
			grid[i][j] = '.'
			pos = (i+di, j+dj)
		elif grid[i+di][j+dj] == '#':
			continue
		elif grid[i+di][j+dj] in '[]':
			# lr is the same
			if di == 0:
				ip, jp = i+di, j+dj
				line = []
				while grid[ip][jp] in '[]':
					line.append(grid[ip][jp])
					ip, jp = ip+di, jp+dj
				if grid[ip][jp] == '#':
					continue
				if grid[ip][jp] != '.':
					print('ERROR', grid[ip][jp], (ip,jp))
					return
				while line:
					grid[ip][jp] = line.pop()
					ip, jp = ip-di, jp-dj
				grid[i+di][j+dj] = '@'
				grid[i][j] = '.'
				pos = (i+di, j+dj)
			# ud must search
			else:
				moveable = True
				movestack = [(i, j)]
				searchq = deque([(i, j)])
				searched = set([(i,j)])
				while searchq:
					#print(searchq, movestack)
					ip,jp = searchq.pop()
					if grid[ip+di][jp+dj] == '#':
						moveable = False
						break
					elif grid[ip+di][jp+dj] == '[':
						if (ip+di, jp+dj) not in searched:
							searched.add((ip+di, jp+dj))
							movestack.append((ip+di, jp+dj))
							searchq.appendleft((ip+di, jp+dj))
						if (ip+di, jp+dj+1) not in searched:
							searched.add((ip+di, jp+dj+1))
							movestack.append((ip+di, jp+dj+1))
							searchq.appendleft((ip+di, jp+dj+1))
					elif grid[ip+di][jp+dj] == ']':
						if (ip+di, jp+dj) not in searched:
							searched.add((ip+di, jp+dj))
							movestack.append((ip+di, jp+dj))
							searchq.appendleft((ip+di, jp+dj))
						if (ip+di, jp+dj-1) not in searched:
							searched.add((ip+di, jp+dj-1))
							movestack.append((ip+di, jp+dj-1))
							searchq.appendleft((ip+di, jp+dj-1))
				#print(movestack)
				if moveable:
					pos = (i+di, j+dj)
					while movestack:
						ip,jp = movestack.pop()
						grid[ip+di][jp+dj] = grid[ip][jp]
						grid[ip][jp] = '.'
	#print('\n'.join([''.join(r) for r in grid]))
	return sum([100*i+j for i,row in enumerate(grid) for j,c in enumerate(row) if c == '['])


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

