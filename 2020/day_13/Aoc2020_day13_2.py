"""
Solution to Advent of Code 2020 day 13 part 2

Chinese remainder theorem
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	s,deps = entries.splitlines()
	s = int(s)
	deps = deps.split(',')

	r = 0
	fac = int(deps[0])
	i = 0
	for f in deps[1:]:
		i += 1
		if f == 'x':
			continue
		f = int(f)
		k = 0
		rem = ((f-i)%f+f)%f
		while (r + k*fac) %f != rem:
			#print((r + k*fac) %f, f, rem)
			k += 1
		r = r + k*fac
		#print(r,f,rem,k,fac)
		fac *= f
	return r


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
