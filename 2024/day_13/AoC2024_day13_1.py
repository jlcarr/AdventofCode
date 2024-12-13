"""
Solution to Advent of Code 2024 day 13 part 1

Solved using regex to parse the unput, then brute-force over the presses for a and b, since we're told they'll be less than 100.
"""
import time
import sys

# tools
import re


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.split('\n\n')
	entries = [e.splitlines() for e in entries]
	#print(entries)
	As = [re.findall(r'Button A: X\+(\d+), Y\+(\d+)',e[0])[0] for e in entries]
	As = [tuple(map(int,e)) for e in As]
	Bs = [re.findall(r'Button B: X\+(\d+), Y\+(\d+)',e[1])[0] for e in entries]
	Bs = [tuple(map(int,e)) for e in Bs]
	Prizes = [re.findall(r'Prize: X=(\d+), Y=(\d+)',e[2])[0] for e in entries]
	Prizes = [tuple(map(int,e)) for e in Prizes]
	#print(As)
	#print(Bs)
	#print(Prizes)
	
	# min cost
	# cost = 3 * a  + b
	# targetX = a * AX + b * BX
	# targetY = a * AY + b * BY
	n = len(As)
	result = 0
	for i in range(n):
		AX, AY = As[i]
		BX, BY = Bs[i]
		PX, PY = Prizes[i]
		subresult = None
		for a in range(100):
			for b in range(100):
				if (PX == a * AX + b * BX) and (PY == a * AY + b * BY):
					if subresult is None or subresult > 3 * a + b:
						subresult = 3 * a + b
		if subresult is not None:
			result += subresult
	return result
				

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

