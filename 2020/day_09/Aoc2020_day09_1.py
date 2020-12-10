"""
Solution to Advent of Code 2020 day 9 part 1

Solved by brute force
Don't see how speedups count be made except via paralellism
"""
import time
import sys


def solution(input_file,s=25):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = list(map(int,entries))
	
	for i, entry in enumerate(entries):
		#print(entry)
		if i < s:
			continue
		#print('check')
		done = False
		for j in range(1,s):
			for k in range(j+1,s+1):
				#print(entries[i-j],entries[i-k],entries[i-j] + entries[i-k],entry)
				if entries[i-j] + entries[i-k] == entry:
					done = True
				if done:
					break
			if done:
				break
		if done:
			continue
		return entry
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	input_2 = int(sys.argv[2]) if len(sys.argv)>2 else 25
	start = time.time()
	answer = solution(input_file,s=input_2)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
