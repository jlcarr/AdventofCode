"""
Solution to Advent of Code 2020 day 7 part 2

Solved by summing the graph recusively
"""
import time
import sys

import re


def search(col,bag_graph):
	result = 1
	#print(col)
	#print(bag_graph[col])
	for c,n in bag_graph[col]:
		result += int(n)*search(c,bag_graph)
	return result

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	entries = entries.splitlines()
	entries = [re.match(r'([\w\s]+) bags contain (.*)\.', entry).groups() for entry in entries]

	bag_graph = dict()
	for parent,child in entries:
		bag_graph[parent] = []
		if child == 'no other bags':
			continue
		for bag in child.split(','):
			n,col = re.match(r' ?(\d)+ (.*) bags?',bag).groups()
			bag_graph[parent].append((col,n))
	#print(bag_graph)
	return search('shiny gold',bag_graph) -1 


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}  ")
	print(f"- **Timing**: {solution_time}  ")
