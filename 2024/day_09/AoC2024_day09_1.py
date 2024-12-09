"""
Solution to Advent of Code 2024 day 9 part 1

Solved by simply building up the disk as ints of file ids or None for free space. Since each block can only be up to size 9 this is linear. We can then run through the disk from the front, and treat it as a stack we can pop from to fill space, as well as always remove free space the from back.
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
	entries = list(map(int,entries))
	#print(entries)
	
	# Solving
	# build disk
	disk = []
	for i,v in enumerate(entries):
		if i % 2 == 0:
			disk += [i//2]*v
		else:
			disk += [None]*v
	#print(disk)
	# fill empty from end
	i = 0
	while disk[-1] is None:
		disk.pop()
	while i < len(disk):
		if disk[i] is None:
			disk[i] = disk[-1]
			disk.pop()
		while disk[-1] is None:
			disk.pop()
		i += 1
	#print(disk)
	
	return sum([i*v for i,v in enumerate(disk)])


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

