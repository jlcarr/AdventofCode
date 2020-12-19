"""
Solution to Advent of Code 2020 day 19 part 1

Parsed rules into regex, the checked matches
"""
import time
import sys

import re

def re_parse(r, ruleset):
	if r == '':
		return ''
	#print("rule",r)
	rule = ruleset[r]
	out = ''
	for r in rule.split('|'):
		for tok in r.split(' '):
			#print(tok)
			if tok == '"a"':
				out += 'a'
			elif tok == '"b"':
				out += 'b'
			else:
				pass
				out += re_parse(tok, ruleset)
		out += '|'
	out = out[:-1]
	if '|' in rule:
		out = '(' + out + ')'
	#print("mapped",out)
	return out

def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()

	rules, mess = entries.split('\n\n')
	rules = dict([(r.split(': ')[0],r.split(': ')[1]) for r in rules.splitlines()])
	mess = mess.splitlines()
	re_string = ""
	#print(rules)
	reg = '^'+re_parse('0',rules)+'$'
	
	#print(reg)
	
	#for l in mess:
	#	print(l,re.match(reg,l))

	return sum([1 for l in mess if re.match(reg,l)])

if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")
