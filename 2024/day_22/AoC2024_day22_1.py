"""
Solution to Advent of Code 2024 day 22 part 1

Solved by just directly implementing the rules. Might be faster using bitwise operations.
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
	entries = [int(e) for e in entries]
	#print(entries)
	
	# Solving
	result = 0
	#entries = [123]
	for e in entries:
		#print(e)
		for i in range(2000):
			e = (e ^ (e * 64)) %  16777216  # e ^ (e << 6) & (1 << 24 - 1)
			e = (e ^ (e // 32)) %  16777216 # e ^ (e >> 5) & (1 << 24 - 1)
			e = (e ^ (e * 2048)) %  16777216  # e ^ (e << 11) & (1 << 24 - 1)
		#print(e)
		result += e
	return result



if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

