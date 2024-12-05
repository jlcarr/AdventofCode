"""
Solution to Advent of Code 2024 day 5 part 1

Solved by simply checking all pairs of pages in each report and seeing if the inverse order of them exists in the set of rules. From there it's easy to get the middle page of each valid report.
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
	ordering,updates = entries.split('\n\n')
	ordering = set([tuple(e.split('|')) for e in ordering.splitlines()])
	
	updates = [e.split(',') for e in updates.splitlines()]
	#print(ordering)
	#print(updates)
	
	# Solving
	result = 0
	for update in updates:
		# check update
		valid = True
		for i in range(len(update)):
			for j in range(i, len(update)):
				if (update[j], update[i]) in ordering:
					valid = False
				if not valid:
					break
			if not valid:
				break
		if valid:
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

