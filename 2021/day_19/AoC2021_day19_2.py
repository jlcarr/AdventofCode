"""
Solution to Advent of Code 2021 day 19 part 2

Same as part 1, except saved time by recording pairs of fixed scanners already checked. Also saved the translations used as well, since that's the scanner's position. Check all pairs of scanners for max distance.
"""
import time
import sys

import re
import numpy as np

dim = 3
rot_mats = []
for x in range(dim):
	remaining = list(range(dim))
	remaining.remove(x)
	for x_sign in [1,-1]:
		for y in remaining:
			z = list(range(dim))
			z.remove(x)
			z.remove(y)
			z = z[0]
			for y_sign in [1,-1]:
				mat = np.zeros((dim,dim), dtype=int)
				mat[0,x] = x_sign
				mat[1,y] = y_sign
				mat[2,:] = np.cross(mat[0,:],mat[1,:])
				rot_mats.append(mat)

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	entries = entries.split('\n\n')
	entries = [scanner.splitlines()[1:] for scanner in entries]
	entries = [[[int(n) for n in position.split(',')] for position in scanner] for scanner in entries]
	entries = [[np.array(position) for position in scanner] for scanner in entries]
	#entries = np.array(entries)

	#for e in entries:
	#	print(e)
	
	#for mat in rot_mats:
	#	print(mat)
	#print(len(rot_mats))
	#return


	fix_beacons = {0: entries[0]}
	entries = entries[1:]

	# cut down the possibilities
	neighbor_candidates = {i:set(range(1+len(entries))) for i in range(1,1+len(entries))}

	positions = []

	found_set = set()
	while len(found_set) < len(entries):
		for number,e in enumerate(entries):
			number = number+1
			if number in found_set:
				continue
			print("searching ",number)
			print("sols", len(fix_beacons))
			found = False
			for mat in rot_mats:
				trans_e = [mat.dot(pos) for pos in e]
				for fix_number,fix in fix_beacons.items():
					if fix_number not in neighbor_candidates[number]:
						continue
				
					fix_set = set([tuple(pos) for pos in fix])
					for fix_point in fix:
						for e_point in trans_e:
							translation = fix_point - e_point
							translated_e = [pos+translation for pos in trans_e]
							#print(translation)
							e_set = set([tuple(pos) for pos in translated_e])
							intersection = e_set.intersection(fix_set)
							if len(intersection) >= 12:
								found = True
								found_set.add(number)
								fix_beacons[number] = translated_e
								positions.append(translation)
								#print("Found", fix_number)
								#print(intersection)
								#print(mat)
								#print(translation)
								#print(sorted(list(fix_beacons.keys())))
								break
						if found: # fix_points
							break
					if found: # fix_beacons
						break
				if found: # rot_mats
					break
			if not found:
				neighbor_candidates[number] -= set(fix_beacons.keys())
		#break

	#all_beacons = set([tuple(b) for beacon_set in fix_beacons.values() for b in beacon_set])
	
	#for b in sorted(list(all_beacons)):
	#	print(b)
	
	sol = 0
	for t1 in positions:
		for t2 in positions:
			if np.sum(np.abs(t1-t2)) > sol:
				sol = np.sum(np.abs(t1-t2))

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

