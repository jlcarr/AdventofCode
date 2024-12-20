"""
Solution to Advent of Code 2024 day 19 part 2

Solved using a trie to quickly tell if a subsequence is amongst the available, and dynamic programming over if each possible position in the target towel is reachable.
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
	base,targets = entries.split('\n\n')
	base = base.split(', ')
	targets = targets.splitlines()
	#print(base)
	#print(targets)
	
	# Setup
	trie = dict()
	for w in base:
		curr = trie
		for c in w:
			if c not in curr:
				curr[c] = dict()
			curr = curr[c]
		curr['END'] = None
	#print(trie)
	
	# Solving
	result = 0
	for w in targets:
		reachable = [False] * (len(w)+1) # have covered all before
		reachable[0] = True
		for i in range(len(w)):
			if not reachable[i]:
				continue
			curr = trie
			j = i
			while j < len(w) and w[j] in curr:
				curr = curr[w[j]]
				j += 1
				if 'END' in curr:
					reachable[j] = True
		#print(w, reachable)
		result += int(reachable[-1])
	
	return result

	# Solving
	kern = np.ones((3), dtype=int)
	def conv_func(arr):
		arr = arr.reshape((3))
		return arr[1]
	entries = scipy.ndimage.generic_filter(entries, conv_func, footprint=kern, mode='constant', cval=0)
	
	sol = 0
	for i,n in enumerate(entries):
		sol += 1
		

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

