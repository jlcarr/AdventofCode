"""
Solution to Advent of Code 2021 day 16 part 1

Basically perform the whole package parsing using lots of binary and hex conversion and string operations.
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
	return 0, bitstring

def parse_packet(bitstring):
	V, bitstring = int(bitstring[:3],2), bitstring[3:]
	T, bitstring = int(bitstring[:3],2), bitstring[3:]
	version_sum = V
	if T == 4:
		sub_version, bitstring = parse_literal(bitstring)
	else:
		length_type_ID, bitstring = bitstring[0], bitstring[1:]
		if length_type_ID == '0':
			pack_lengths, bitstring = int(bitstring[:15],2), bitstring[15:]
			sub_packets, bitstring = bitstring[:pack_lengths], bitstring[pack_lengths:]
			while sub_packets:
				sub_version, sub_packets = parse_packet(sub_packets)
				version_sum += sub_version
		else:
			number_packets, bitstring = int(bitstring[:11],2), bitstring[11:]
			for i in range(number_packets):
				sub_version, bitstring = parse_packet(bitstring)
				version_sum += sub_version
	return version_sum, bitstring


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()
	
	# Parsing
	#print(entries)
	packet = ''.join([bin(int(e,16))[2:].rjust(4,'0') for e in entries])
	#print(packet)

	version_sum, bitstring = parse_packet(packet)

	return version_sum

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

