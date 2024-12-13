"""
Solution to Advent of Code 2024 day 13 part 2

Solved using z3 to perform the integer optimization problem and also check for unsatisfiable cases. However we can solve this problem with linear algebra for the 2 variable system and the the solutions are integer. The case of being collinear results in the linear diophantine equation solveable by Bezout's identity. However, the collinear case never actually appeared in the input, and so only simple linear algebra was needed!
"""
import time
import sys

# tools
import re
import z3


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
	Prizes = [tuple([v+10000000000000 for v in e]) for e in Prizes]
	#print(As)
	#print(Bs)
	#print(Prizes)
	
	# min cost
	# cost = 3 * a + b
	# targetX = a * AX + b * BX
	# targetY = a * AY + b * BY
	
	# targetX * AY - targetY * AX == b * (BX * AY - BY * AX)
	# targetX * BY - targetY * BX == a * (BY * AX - BX * AY)
	
	# targetX = |AX BX| a
	# targetY = |AY BY| b
	# collinear if AY/AX = BY/BX -> AY * BX = BY * AX
	n = len(As)
	result = 0
	for i in range(n):
		AX, AY = As[i]
		BX, BY = Bs[i]
		PX, PY = Prizes[i]
		
		solver = z3.Optimize()
		a = z3.Int("a")
		b = z3.Int("b")
		solver.add(a >= 0)
		solver.add(b >= 0)
		solver.add(PX == a * AX + b * BX)
		solver.add(PY == a * AY + b * BY)
		solver.minimize(3*a+b)
		
		if solver.check() == z3.sat:
			model = solver.model()
			#print(i, model.eval(a), model.eval(b))
			result += model.eval(3*a+b).as_long()
			
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

