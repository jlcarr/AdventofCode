"""
Solution to Advent of Code 2020 day 4 part 1

Solved by brute force
Don't see how speedups count be made except via paralellism
"""
import time
import sys

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.split('\n\n')
	valid = [p for p in entries if all([f in p for f in ['byr:','iyr:','eyr:','hgt:','hcl:','ecl:','pid:']])]
	return len(valid)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
