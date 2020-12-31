"""
Solution to Advent of Code 2020 day 25 part 1

Brute force Diffie-Helman, with ~20million possibilities
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	p1,p2 = entries.splitlines()
	p1 = int(p1)
	p2 = int(p2)
	#print(p1,p2)

	subj = 1
	loop = 0
	while subj != p1 and subj != p2:
		loop += 1
		subj = (subj*7)%20201227
		#print(subj,p1,p2)
		#break
	co = p1 if subj == p2 else p2

	subj = 1
	for i in range(loop):
		subj = (subj*co)%20201227

	return subj

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
