"""
Solution to Advent of Code 2024 day 17 part 2

Solved by analyzing the code to see it ends with a jump to make a loop in which 1 value is output each time. Therefore we know the number of times the loop must execute is the same as the length of the program itself, and each output must be equal to the instruction corresponding to the loop number. We can therefore put these constraints in z3, using 64 bit BitVecs for each register's value at each loop and instruction's place.
"""
import time
import sys

# tools
import z3


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	RA = int(entries[0].split(': ')[-1])
	RB = int(entries[1].split(': ')[-1])
	RC = int(entries[2].split(': ')[-1])
	prog = entries[4].split(': ')[-1].split(',')
	prog = [int(p) for p in prog]
	#print(RA)
	#print(RB)
	#print(RC)
	#print(prog)
	
	# Solving
	def combo(v, RA, RB, RC):
		if 0 <= v <= 3:
			return v
		elif v == 4:
			return RA
		elif v == 5:
			return RB
		elif v == 6:
			return RC
		elif v == 7:
			print("INVALID COMBO")
			return
		print("COMBO OOB")
		return
	
	solver = z3.Optimize()
	RAs = [z3.BitVec(f"RA_init", 64)]
	RBs = [0]
	RCs = [0]
	for ip in range(len(prog)):
		for i in range(0,len(prog),2):
			if prog[i] == 0: # adv
				RAs.append(z3.BitVec(f"RA_{ip}_{i}", 64))
				solver.add(RAs[-1] == RAs[-2] >> combo(prog[i+1], RAs[-2], RBs[-1], RCs[-1]))
			elif prog[i] == 1: # bxl
				RBs.append(z3.BitVec(f"RB_{ip}_{i}", 64))
				solver.add(RBs[-1] == RBs[-2] ^ prog[i+1])
			elif prog[i] == 2: # bst
				RBs.append(z3.BitVec(f"RB_{ip}_{i}", 64))
				solver.add(RBs[-1] == combo(prog[i+1], RAs[-1], RBs[-2], RCs[-1]) % 8)
			elif prog[i] == 3: # jnz
				if RA == 0:
					pass
					#i += 2
				else:
					#i = prog[i+1]
					pass
			elif prog[i] == 4: # bxc
				RBs.append(z3.BitVec(f"RB_{ip}_{i}", 64))
				solver.add(RBs[-1] == RBs[-2] ^ RCs[-1])
			elif prog[i] == 5: # out
				solver.add(prog[ip] == combo(prog[i+1], RAs[-1], RBs[-1], RCs[-1]) % 8)
			elif prog[i] == 6: # bdv
				RBs.append(z3.BitVec(f"RB_{ip}_{i}", 64))
				solver.add(RBs[-1] == RAs[-1] >> combo(prog[i+1], RAs[-1], RBs[-2], RCs[-1]))
			elif prog[i] == 7: # cdv
				RCs.append(z3.BitVec(f"RC_{ip}_{i}", 64))
				solver.add(RCs[-1] == RAs[-1] >> combo(prog[i+1], RAs[-1], RBs[-1], RCs[-2]))
			else:
				print('INVALID PROG', i, prog[i], prog[i+1])
			#if len(out) > len(prog):
			#	break
	solver.minimize(RAs[0])
	#print(solver.assertions())
	if solver.check() == z3.sat:
		model = solver.model()
		return model.eval(RAs[0]).as_long()
	
	return None


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

