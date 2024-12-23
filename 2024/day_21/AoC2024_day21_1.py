"""
Solution to Advent of Code 2024 day 21 part 2

Solved using Dijkstra's algorithm with heapq, and careful keeping track of and updating of the states of all 3 robots.
"""
import time
import sys

# tools
import heapq


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	#entries = [list(e) for e in entries]
	#print(entries)
	
	npad = [
		['7','8','9'],
		['4','5','6'],
		['1','2','3'],
		[' ','0','A'],
	]
	dpad = [
		[' ','^','A'],
		['<','v','>'],
	]
	
	dmap = {
		'^': (-1,0),
		'v': (1,0),
		'<': (0,-1),
		'>': (0,1),
	}

	# state (r1,r2,r3) = 5 * 5 * 11
	result = 0
	for code in entries:
		state = ((0,2), (0,2), (3,2))
		costs = {state: 0}
		prevs = dict()
		q = [(0,state)]
		codecost = 0
		for d in code:
			while q:
				cost, state = heapq.heappop(q)
				((ir1,jr1), (ir2,jr2), (ir3,jr3)) = state
				#print(d)
				#print(cost, state)
				#print(dpad[ir1][jr1], dpad[ir2][jr2], npad[ir3][jr3])
				#if dpad[ir1][jr1] == 'A' and dpad[ir2][jr2] == 'A' and npad[ir3][jr3] == d
				#	break
				# move
				for k,(dir1,djr1) in dmap.items():
					if (0 <= ir1+dir1 < 2) and (0 <= jr1+djr1 < 3) and dpad[ir1+dir1][jr1+djr1] != ' ':
						newstate = ((ir1+dir1,jr1+djr1), (ir2,jr2), (ir3,jr3))
						if newstate not in costs:
							costs[newstate] = cost + 1
							heapq.heappush(q, (cost + 1, newstate))
							prevs[newstate] = (state, (k,' ',' '))
				# you enter
				if dpad[ir1][jr1] in dmap:
					dir2,djr2 = dmap[dpad[ir1][jr1]]
					if (0 <= ir2+dir2 < 2) and (0 <= jr2+djr2 < 3) and dpad[ir2+dir2][jr2+djr2] != ' ':
						newstate = ((ir1,jr1), (ir2+dir2,jr2+djr2), (ir3,jr3))
						if newstate not in costs:
							costs[newstate] = cost + 1
							heapq.heappush(q, (cost + 1, newstate))
							prevs[newstate] = (state, ('A',dpad[ir1][jr1],' '))
				# you enter r1 enter
				elif dpad[ir1][jr1] == 'A':
					if dpad[ir2][jr2] in dmap:
						dir3,djr3 = dmap[dpad[ir2][jr2]]
						if (0 <= ir3+dir3 < 4) and (0 <= jr3+djr3 < 3) and npad[ir3+dir3][jr3+djr3] != ' ':
							newstate = ((ir1,jr1), (ir2,jr2), (ir3+dir3,jr3+djr3))
							if newstate not in costs:
								costs[newstate] = cost + 1
								heapq.heappush(q, (cost + 1, newstate))
								prevs[newstate] = (state, ('A',dpad[ir1][jr1],dpad[ir2][jr2]))
					# you enter r1 enter r2 enter
					elif dpad[ir2][jr2] == 'A':
						if npad[ir3][jr3] == d:
							codecost = cost+1 # digit cost
							costs = {state: cost+1}
							q = [(cost+1, state)]
							
							#yps = ['A']
							#r1ps = ['A']
							#r2ps = ['A']
							#currs = []
							#curr = state
							#while curr in prevs:
							#	print(curr)
							#	curr, (yp,r1p,r2p) = prevs[curr]
							#	currs.append(curr)
							#	yps.append(yp)
							#	r1ps.append(r1p)
							#	r2ps.append(r2p)
							#print('yo press:', ''.join(yps[::-1]))
							#print('r1 press:', ''.join(r1ps[::-1]))
							#print('r2 press:', ''.join(r2ps[::-1]))
							#print('r1 state:', ''.join([dpad[r1[0]][r1[1]] for (r1,r2,r3) in currs[::-1]]))
							#print('r2 state:', ''.join([dpad[r2[0]][r2[1]] for (r1,r2,r3) in currs[::-1]]))
							#print('r3 state:', ''.join([npad[r3[0]][r3[1]] for (r1,r2,r3) in currs[::-1]]))
							prevs = dict()
							break
			#print(d, codecost)
			#break
			#return
		#print(codecost)
		result += codecost * int(code[:-1])
	return result

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

