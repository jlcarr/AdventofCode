"""
Solution to Advent of Code 2020 day 23 part 1

Modular arithmetic
"""
import time
import sys




def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = list(entries)[:-1]
	entries = list(map(int,entries))
	#print(entries)

	curr = entries[0]
	for t in range(100):
		dest = curr-1
		i_curr = entries.index(curr)
		picked = [entries[(i_curr+1)%len(entries)],
			entries[(i_curr+2)%len(entries)],
			entries[(i_curr+3)%len(entries)]]
		for v in picked:
			entries.remove(v)
		#print(entries,picked)
		while dest not in entries and dest >=1:
			dest -= 1
		if dest not in entries:
			dest = max(entries)
		i = entries.index(dest)
		entries = entries[:i+1] + picked + entries[i+1:]
		#print(curr, entries,picked, dest)
		curr = entries[(entries.index(curr)+1)%len(entries)]

	one_index = entries.index(1)

	return ''.join(map(str,entries[one_index+1:]+entries[:one_index]))

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
