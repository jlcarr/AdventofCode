"""
Solution to Advent of Code 2020 day 23 part 2

linked lists and a dict mapping
"""
import time
import sys


class LL():
	def __init__(self, v, next = None, prev = None):
		self.v = v
		self.next = next
		self.prev = prev
	def disp(self):
		curr = self
		s = self.v
		print(s,",",end='')
		curr = curr.next
		while curr.v != s:
			print(curr.v,",",end='')
			curr = curr.next
		print()

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = list(entries)[:-1]
	entries = list(map(int,entries))
	#print(entries)
	entries += list(range(len(entries)+1,1000000+1))
	max_key = max(entries)
	#print(max_key,"KEY")

	vals_map = dict()
	for e in entries:
		vals_map[e] = LL(e)
	for i,e in enumerate(entries):
		vals_map[e].next = vals_map[entries[(i+1)%len(entries)]]
	for i,e in enumerate(entries):
		vals_map[entries[(i+1)%len(entries)]].prev = vals_map[e]

	curr = entries[0]
	for t in range(10000000):
		#if t % (1000*100) == 0:
			#print(t,"TURN")
		dest = curr-1
		picked = [vals_map[curr].next.v,
			vals_map[curr].next.next.v,
			vals_map[curr].next.next.next.v]
		vals_map[curr].next = vals_map[curr].next.next.next.next
		vals_map[curr].next.prev = vals_map[curr]
		while dest in picked and dest >=1:
			dest -= 1
		if dest in picked or dest < 1:
			dest = max_key
			while dest in picked and dest >=1:
				dest -= 1
		#print(dest,"DEST", curr,"CURR", picked)
		LL_dest = vals_map[dest]
		LL_dest.next.prev = vals_map[picked[-1]]
		vals_map[picked[-1]].next = LL_dest.next
		LL_dest.next = vals_map[picked[0]]
		LL_dest.next.prev = LL_dest
		curr = vals_map[curr].next.v
		#vals_map[curr].disp()

	c = vals_map[1].next
	#print(c.v,c.next.v)

	return c.v*c.next.v

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
