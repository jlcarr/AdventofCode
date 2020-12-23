"""
Solution to Advent of Code 2020 day 22 part 2


"""
import time
import sys

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	p1,p2 = entries.split('\n\n')
	p1 = list(map(int,p1.splitlines()[1:]))
	p2 = list(map(int,p2.splitlines()[1:]))
	#print(p1,p2)

	while p1 and p2:
		#print(p1,p2)
		p1_c = p1[0]
		p1 = p1[1:]
		p2_c = p2[0]
		p2 = p2[1:]
		if p1_c >p2_c:
			p1.append(p1_c)
			p1.append(p2_c)
		else:
			p2.append(p2_c)
			p2.append(p1_c)

	r = p1 if p1 else p2
	r = r[::-1]
	res = sum([(i+1)*v for i,v in enumerate(r)])

	return res

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
