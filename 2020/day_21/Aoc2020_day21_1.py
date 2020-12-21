"""
Solution to Advent of Code 2020 day 21 part 1

Set logic: set intersection helps obtain possibilities for each alergen, set union gets all ingredients, then set difference gives all allergen-free.
"""
import time
import sys


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	r = []
	for e in entries:
		e = e.split(' (contains ')
		ings = e[0].split(' ')
		alers = []
		if len(e)>1:
			alers = e[1][:-1].split(', ')
		r.append((ings,alers))
	#print(r)
	entries = r


	ing_set = set()
	aler_map = dict()
	for line in entries:
		ings, alers = line
		for a in alers:
			if a not in aler_map:
				aler_map[a] = set(ings)
			aler_map[a] &= set(ings)
		ing_set |= set(ings)
	#print(aler_map)
	aler_free = ing_set
	for vs in aler_map.values():
		aler_free -= vs
	#print(aler_free)

	count = 0
	for line in entries:
		ings, alers = line
		count += len(set(ings) & aler_free)

	return count

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
