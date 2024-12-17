"""
Solution to Advent of Code 2024 day 17 part 1

Solved by simply implementing the instruction set and keeping track of the outputs to join and return.
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
			
	out = []
	i = 0
	while i < len(prog):
		if prog[i] == 0: # adv
			RA = RA // (2**combo(prog[i+1], RA, RB, RC))
			i += 2
		elif prog[i] == 1: # bxl
			RB = RB ^ prog[i+1]
			i += 2
		elif prog[i] == 2: # bst
			RB = combo(prog[i+1], RA, RB, RC) % 8
			i += 2
		elif prog[i] == 3: # jnz
			if RA == 0:
				pass
				i += 2
			else:
				i = prog[i+1]
		elif prog[i] == 4: # bxc
			RB = RB ^ RC
			i += 2
		elif prog[i] == 5: # out
			out.append(combo(prog[i+1], RA, RB, RC) % 8)
			i += 2
		elif prog[i] == 6: # bdv
			RB = RA // (2**combo(prog[i+1], RA, RB, RC))
			i += 2
		elif prog[i] == 7: # cdv
			RC = RA // (2**combo(prog[i+1], RA, RB, RC))
			i += 2
		else:
			print('INVALID PROG', i, prog[i], prog[i+1])
	return ','.join(list(map(str,out)))


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

