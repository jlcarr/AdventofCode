"""
Solution to Advent of Code 2024 day 4 part 1

Solved usual word search approach, but only looking for 1 word, check every possible starting position, over all directions, go along the word checking all letters match. Careful for hitting the puzzle edge.
"""
import time
import sys

# tools
# none


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [list(e) for e in entries]
	#print(entries)
	
	target = 'XMAS'
	sol = 0
	for i in range(len(entries)):
		for j in range(len(entries[0])):
			for di in [-1,0,1]:
				for dj in [-1,0,1]:
					if di == 0 and dj == 0:
						continue
					ip,jp = i,j
					found = False
					for k,c in enumerate(target):
						#if (i,j, di,dj) == (0,2, 1,1):
						#	print(k,c,entries[ip][jp])
						if entries[ip][jp] != c:
							break
						if k+1 == len(target):
							found = True
						ip += di
						jp += dj
						if not ((0 <= ip < len(entries)) and (0 <= jp < len(entries[0]))):
							break
					if found:
						#print('FOUND',i,j, di,dj)
						sol += 1
	return sol


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

