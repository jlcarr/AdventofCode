"""
Solution to Advent of Code 2020 day 11 part 2

Brute force
Use a loop to check all directions
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = list(map(list,entries))
	#print(entries)

	change = True
	while change:
		#for row in entries:
		#	print(''.join(row))
		#print()
		#print(entries)
		change = False
		nex = [[col for col in row] for row in entries]
		for i,row in enumerate(entries):
			for j,col in enumerate(row):
				count = 0
				
				for i_p in [-1,0,1]:
					for j_p in [-1,0,1]:
						if i_p == 0 and j_p == 0:
							continue
						i_c = 1
						j_c = 1
						while i_p*i_c+i >=0 and j_p*j_c+j >=0 and i_p*i_c+i < len(entries) and j_p*j_c+j < len(row):
							if entries[i_p*i_c+i][j_p*j_c+j] == '#':
								count += 1
								break
							if entries[i_p*i_c+i][j_p*j_c+j] == 'L':
								break
							i_c += 1
							j_c += 1
				if col == 'L' and count ==0:
					nex[i][j] = '#'
					change = True
				if col == '#' and count >=5:
					nex[i][j] = 'L'
					change = True
		entries = nex
	return sum([1 for row in entries for col in row if col == '#'])
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
