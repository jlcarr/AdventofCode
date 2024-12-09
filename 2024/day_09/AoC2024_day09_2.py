"""
Solution to Advent of Code 2024 day 9 part 2

Solved using heapq as a priority queue for each space size (there are only 9 after all) to find the lowest index at which they can be placed. We just need to run through them checking for the lowest index available which fits each block. After a block is moved, if there is leftover space where it was moved, then this new index is added to it's size's queue.
"""
import time
import sys

# tools
import heapq


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = list(map(int,entries))
	#print(entries)
	
	disk = []
	for i,v in enumerate(entries):
		if i % 2 == 0:
			disk += [i//2]*v
		else:
			disk += [None]*v
	#print(disk)
	
	# Setup
	# for each of the 9 possible sizes, heap of min start loc
	places = [[] for _ in range(10)]
	p = 0
	for i,v in enumerate(disk):
		if v is not None:
			size = i - p
			if size > 0:
				heapq.heappush(places[size], p)
			p = i+1
	#print(places)
	# get the file blocks with their ids, start and end positions in a stack
	tomoves = []
	disk.append(None)
	pid = disk[0]
	pi = 0
	for i,id in enumerate(disk):
		if id != pid:
			if pid is not None:
				tomoves.append((pid,pi,i))
			pi = i
			pid = id
	#print(tomoves)
	
	# Solving
	while tomoves:
		id, s, e = tomoves.pop()
		size = e - s
		# Find the lowest index place which fits
		index = None
		sizeused = None
		for candidate_sizeused in range(10):
			if candidate_sizeused >= size and places[candidate_sizeused] and places[candidate_sizeused][0] < s:
				if index is None or index > places[candidate_sizeused][0]:
					index = places[candidate_sizeused][0]
					sizeused = candidate_sizeused
		# Place it there and update the heap for any remaining space
		if index is not None:
			index = heapq.heappop(places[sizeused])
			disk[index:index+size] = [id]*size
			disk[s:e] = [None]*size
			sizerem = sizeused - size
			if sizerem > 0:
				heapq.heappush(places[sizerem], index+size)
	#print(disk)
	
	return sum([i*v for i,v in enumerate(disk) if v is not None])
	

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

