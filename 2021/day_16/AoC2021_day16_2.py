"""
Solution to Advent of Code 2021 day 16 part 2

Same as part one, but added an operator evaluation.
"""
import time
import sys

import re
import numpy as np

def parse_literal(bitstring):
	fin_string = ''
	while bitstring[0] != '0':
		fin_add, bitstring = bitstring[1:5], bitstring[5:]
		fin_string += fin_add
	fin_add, bitstring = bitstring[1:5], bitstring[5:]
	fin_string += fin_add
	value = int(fin_string, 2)
	#print(value)
	return value, bitstring

def operator(ID, values):
	if ID == 0:
		return sum(values)
	elif ID == 1:
		rval = 1
		for v in values:
			rval *= v
		return rval
	elif ID == 2:
		return min(values)
	elif ID == 3:
		return max(values)
	elif ID == 5:
		return int(values[0] > values[1])
	elif ID == 6:
		return int(values[0] < values[1])
	elif ID == 7:
		return int(values[0] == values[1])

def parse_packet(bitstring):
	V, bitstring = int(bitstring[:3],2), bitstring[3:]
	T, bitstring = int(bitstring[:3],2), bitstring[3:]
	value = 0
	if T == 4:
		value, bitstring = parse_literal(bitstring)
	else:
		length_type_ID, bitstring = bitstring[0], bitstring[1:]
		if length_type_ID == '0':
			pack_lengths, bitstring = int(bitstring[:15],2), bitstring[15:]
			sub_packets, bitstring = bitstring[:pack_lengths], bitstring[pack_lengths:]
			sub_values = []
			while sub_packets:
				sub_val, sub_packets = parse_packet(sub_packets)
				sub_values.append(sub_val)
			value = operator(T, sub_values)
		else:
			number_packets, bitstring = int(bitstring[:11],2), bitstring[11:]
			sub_values = []
			for i in range(number_packets):
				sub_val, bitstring = parse_packet(bitstring)
				sub_values.append(sub_val)
			value = operator(T, sub_values)
	return value, bitstring


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()
	
	# Parsing
	#print(entries)
	packet = ''.join([bin(int(e,16))[2:].rjust(4,'0') for e in entries])
	#print(packet)

	sol, bitstring = parse_packet(packet)

	return sol

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

