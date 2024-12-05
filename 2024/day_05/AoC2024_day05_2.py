"""
Solution to Advent of Code 2024 day 5 part 2

Solved similar to part 1, except which there is an invalid pairing, swap the elements, and then recheck until a valid ordering is reached. Note that a topological sort does not work, because there are cycles in the rules: updates must be generated so as not to contain one such cycle!
"""
import time
import sys

# tools
#none


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	ordering,updates = entries.split('\n\n')
	ordering = set([tuple(e.split('|')) for e in ordering.splitlines()])
	
	updates = [e.split(',') for e in updates.splitlines()]
	#print(ordering)
	#print(updates)
	
	# Solving
	result = 0
	for update in updates:
		# check update
		wasntvalid = False
		valid = False
		while not valid:
			valid = True
			for i in range(len(update)):
				for j in range(i, len(update)):
					if (update[j], update[i]) in ordering:
						wasntvalid = True
						valid = False
						#swap
						temp = update[i]
						update[i] = update[j]
						update[j] = temp
					if not valid:
						break
				if not valid:
					break
		if wasntvalid:
			if len(update) % 2 != 1:
				print('UNEVEN', update)
			result += int(update[len(update)//2])
		# get middle
	
	return result


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

