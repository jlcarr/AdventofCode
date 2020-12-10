"""
Solution to Advent of Code 2020 day 10 part 2

Solved by dynamic programming (memoizing sub-problems)
Make sure to sort first!
"""
import time
import sys

sub_sols = dict()

def search(val):
	#print(val)
	if val == [0]:
		return 1
	if len(val) in sub_sols:
		return sub_sols[len(val)]
	result = 0
	i = 1
	while (len(val) > i) and (val[-1] - val[-1-i] <=3):
		result += search(val[:-i])
		i+=1
	sub_sols[len(val)] = result
	return result

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	
	
	entries = list(map(int,entries))
	entries = sorted(entries)
	entries = [0] + entries + [max(entries)+3]

	return search(entries)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
