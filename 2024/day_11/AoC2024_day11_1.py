"""
Solution to Advent of Code 2024 day 11 part 1

Solved by reconstructing the array each step, by running through the old and appending to a Python list the new values.
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
	entries = entries.split(' ')
	entries = [int(e) for e in entries]
	#print(entries)

	# Solving
	for i in range(25):
		new = []
		for v in entries:
			if v == 0:
				new.append(1)
			elif len(str(v)) % 2 == 0:
				v = str(v)
				new.append(int(v[:len(v)//2]))
				new.append(int(v[len(v)//2:]))
			else:
				new.append(v*2024)
		entries = new
	#print(entries)
	return len(entries)


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

