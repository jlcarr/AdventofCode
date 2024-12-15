"""
Solution to Advent of Code 2024 day 15 part 1

Solved by performing the simulation, when a box is pushed we keep checking forward for if there is a wall or empty space at the end: a line of boxes moving forward is the same as the empty space being filled with a box and the robot replacing the immediate one it pushed.
"""
import time
import sys

# tools
# None


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	grid, moves = entries.split('\n\n')
	grid = [list(l) for l in grid.splitlines()]
	moves = moves.replace('\n','')
	#print('\n'.join([''.join(r) for r in grid]))
	#print(moves)
	pos = [(i,j) for i,row in enumerate(grid) for j,c in enumerate(row) if c == '@'][0]
	#print(pos)
	
	mmap = {'>':(0,1), '<':(0,-1), '^':(-1,0), 'v':(1,0)}
	for m in moves:
		di,dj = mmap[m]
		i,j = pos
		if grid[i+di][j+dj] == '.':
			grid[i+di][j+dj] = '@'
			grid[i][j] = '.'
			pos = (i+di, j+dj)
		elif grid[i+di][j+dj] == '#':
			continue
		elif grid[i+di][j+dj] == 'O':
			ip, jp = i+di, j+dj
			while grid[ip][jp] == 'O':
				ip, jp = ip+di, jp+dj
			if grid[ip][jp] == '#':
				continue
			if grid[ip][jp] != '.':
				print('ERROR', grid[ip][jp], (ip,jp))
				return
			grid[ip][jp] = 'O'
			grid[i+di][j+dj] = '@'
			grid[i][j] = '.'
			pos = (i+di, j+dj)
	#print('\n'.join([''.join(r) for r in grid]))
	
	return sum([100*i+j for i,row in enumerate(grid) for j,c in enumerate(row) if c == 'O'])


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

