"""
Solution to Advent of Code 2020 day 21 part 2

Cut out alergy-free set of all possibilities. Then use similar approach to day 16-2.
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
	aler_free = ing_set.copy()
	for vs in aler_map.values():
		aler_free -= vs
	#print("ALER FREE",aler_free)
	#print("ALER MAP",aler_map)
	#print(ing_set)

	for k in list(aler_map.keys()):
		aler_map[k] -= aler_free

	change = True
	while change:
		change = False
		for a,ings in list(aler_map.items()):
			if len(ings) == 1:
				i = next(iter(ings))
				for a1 in list(aler_map.keys()):
					if len(aler_map[a1])>1 and i in aler_map[a1]:
						aler_map[a1].remove(i)
						change = True
	#print(aler_map)
	sort_keys = sorted(list(aler_map.keys()))
	fin = [aler_map[k].pop() for k in sort_keys]
	fin = ','.join(fin)

	return fin

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
