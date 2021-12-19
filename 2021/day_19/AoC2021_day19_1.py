"""
Solution to Advent of Code 2021 day 19 part 1

Construct the rotation matrices by permuting the x and y axes, then cross product to get z. Then iterate over all the remaining scanners, over rotations, and get possible translations by matching pairs of beacons to check if at least 12 match up.
Might have been sped up using more numpy instead of explicit iterations
Faster solution would be to record distances between points in a cube, and use the set itersection to match
This approach would be "tricked" by mirroring, so a proper check would need to be done as well.
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

	#for e in entries:
	#	print(e)
	
	#for mat in rot_mats:
	#	print(mat)
	#print(len(rot_mats))
	#return

	# Test check
	#e = entries[2]
	#for mat in rot_mats:
	#	trans_e = [mat.dot(pos) for pos in e]
	#	translation = np.array([1105,-1205,1229])
	#	translated_e = [pos+translation for pos in trans_e]
	#	all_beacons = set([tuple(b) for b in translated_e])
	#	translated_e = sorted(list(all_beacons))
	#	print(mat)
	#	print(translated_e)
	#return None


	fix_beacons = {0: entries[0]}
	entries = entries[1:]

	found_set = set()
	while len(found_set) < len(entries):
		for number,e in enumerate(entries):
			number = number+1
			if number in found_set:
				continue
			print("searching",number)
			print("found", len(fix_beacons))
			found = False
			for mat in rot_mats:
				trans_e = [mat.dot(pos) for pos in e]
				for fix_number,fix in fix_beacons.items():
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
		#break

	all_beacons = set([tuple(b) for beacon_set in fix_beacons.values() for b in beacon_set])
	
	#for b in sorted(list(all_beacons)):
	#	print(b)

	return len(all_beacons)

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

