"""
Solution to Advent of Code 2024 day 22 part 2

Solved using a deque for the queue of differences, and a dictionary to sum the values for each pattern, and a set to not repeat the pattern within each buyer's pattern.
"""
import time
import sys

# tools
from collections import deque


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.splitlines()
	entries = [int(e) for e in entries]
	#print(entries)
	
	result = 0
	#entries = [123]
	seq_vals = dict()
	for e in entries:
		#print(e)
		seq = deque()
		prev = e
		seen = set()
		for i in range(2000):
			e = (e ^ (e * 64)) %  16777216  # e ^ (e << 6) & (1 << 24 - 1)
			e = (e ^ (e // 32)) %  16777216 # e ^ (e >> 5) & (1 << 24 - 1)
			e = (e ^ (e * 2048)) %  16777216  # e ^ (e << 11) & (1 << 24 - 1)
			
			#print(e, (e%10)-(prev%10))
			seq.append((e%10)-(prev%10))
			if len(seq) > 4:
				seq.popleft()
			tseq = tuple(seq)
			if len(tseq) == 4 and tseq not in seen:
				seen.add(tseq)
				if tseq not in seq_vals:
					seq_vals[tseq] = 0
				seq_vals[tseq] += e % 10
			prev = e
		#print(e)
	#print()
	#print(len(seqs))
	#print(seq_vals)
	return max(seq_vals.values())
	
	# len(entries) * 2000
	# 1665 * 2000 = 3,330,000


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

