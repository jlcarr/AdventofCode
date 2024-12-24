"""
Solution to Advent of Code 2024 day 24 part 2

Solved using GraphViz to draw the graph and ensure it is a simple full adder, then run through the full adder cells by their x and y inputs, saving the carry from before, and constructing the iternal values, and checking they are feeding forward into the correct places. At any mismatches I inspected the GraphViz to see the correct. I also implemented automated corrections for the types needed for my input. After a correction is made rerun the search to get further down the chain of adder cells.
"""
import time
import sys

# tools
#import math
#None


def solution(input_file):
	with open(input_file,'r') as file:
		entries = file.read()
	entries = entries.strip()

	# Parsing
	defaults, connections = entries.split('\n\n')
	
	defaults = dict([v.split(': ') for v in defaults.splitlines()])
	
	connections = [v.split(' -> ') for v in connections.splitlines()]
	connections = [(tuple(ex.split(' ')),out) for ex,out in connections]
	
	#print(defaults)
	#print(connections)
	
	
	invconnections = {out: ins for ins,out in connections}
	#print(invconnections)

	allnodes = set(defaults.keys()) | set(invconnections.keys()) | set([l for (l,op,r),out in connections]) | set([r for (l,op,r),out in connections])
	#print(allnodes)
	
	zs = sorted([node for node in allnodes if node.startswith('z')])
	#print(zs)
	
	#print(len([node for node in allnodes if not node.startswith('x') and not node.startswith('y')]))
	#print(len(connections))
	# 222 output wires
	# choose(n,8) * choose(8,choose 2) * choose(6,choose 2) * choose(4,choose 2) * 1
	#print(math.comb(222,8) * math.comb(8,2) * math.comb(6,2) * math.comb(4,2))
	# 324,564,114,035,561,400
	#print([v for v in defaults.keys() if not v.startswith('x') and not v.startswith('y')])
	
	#graphviz = []
	#for (l,op,r),out in connections:
	#	graphviz.append(f"{l} -> {op}{l}{r};")
	#	graphviz.append(f"{r} -> {op}{l}{r};")
	#	graphviz.append(f"{op}{l}{r} -> {out};")
	#	graphviz.append(f"")
	#with open('viz.dot', 'w') as f:
	#	f.write('\n'.join(graphviz))
	
	connections = dict(connections)
	#print(connections)
	
	# corrections
	#connections[('x05','AND','y05')] = 'grf'
	#connections[('x05','XOR','y05')] = 'wpq'
	
	#connections[('ffh','XOR','gdw')] = 'z18'
	#connections[('cjb','OR','kqr')] = 'fvw'
	
	#connections[('nwg','XOR','fsf')] = 'z22'
	#connections[('nwg','AND','fsf')] = 'mdb'
	
	#connections[('svb','XOR','fsw')] = 'z36'
	#connections[('y36','AND','x36')] = 'nwq'
	
	n = max([int(k[1:]) for k in invconnections.keys() if k.startswith('z')])
	result = []
	for iswap in range(4):
		p_carry = connections[(f'y00', 'AND', f'x00')]
		for i in range(1,n):
			# check
			# xy_sum = x ^ y
			# xy_carry = x & y
			# z = xy_sum ^ p_carry
			# pxy_carry = xy_sum & p_carry
			# carry = xy_carry | pxy_carry
			
			#print(i)
			#print((f'x{i:02}', 'XOR', f'y{i:02}'))
			if (f'x{i:02}', 'XOR', f'y{i:02}') in connections:
				xy_sum = connections[(f'x{i:02}', 'XOR', f'y{i:02}')]
			elif (f'y{i:02}', 'XOR', f'x{i:02}') in connections:
				xy_sum = connections[(f'y{i:02}', 'XOR', f'x{i:02}')]
			else:
				#print('UNFOUND')
				return
			#print('xy_sum:', xy_sum)
			#print()
			
			#print((f'x{i:02}', 'AND', f'y{i:02}'))
			if (f'x{i:02}', 'AND', f'y{i:02}') in connections:
				xy_carry = connections[(f'x{i:02}', 'AND', f'y{i:02}')]
			elif (f'y{i:02}', 'AND', f'x{i:02}') in connections:
				xy_carry = connections[(f'y{i:02}', 'AND', f'x{i:02}')]
			else:
				#print('UNFOUND')
				return
			#print('xy_carry:', xy_carry)
			#print()
			
			#print(f'z{i:02} = xy_sum ^ p_carry', (xy_sum, 'XOR', p_carry))
			if (xy_sum, 'XOR', p_carry) in connections and connections[(xy_sum, 'XOR', p_carry)] != f'z{i:02}':
				#print('FOUND!')
				pair = [f'z{i:02}', connections[(xy_sum, 'XOR', p_carry)]]
				#print(pair)
				p0,p1 = invconnections[pair[0]], invconnections[pair[1]]
				invconnections[pair[0]], invconnections[pair[1]] = p1, p0
				connections[p0],connections[p1] = pair[1], pair[0]
				result += pair
				#print()
				break
			elif (p_carry, 'XOR', xy_sum) in connections and connections[(p_carry, 'XOR', xy_sum)] != f'z{i:02}':
				#print('FOUND!')
				pair = [f'z{i:02}', connections[(p_carry, 'XOR', xy_sum)]]
				#print(pair)
				p0,p1 = invconnections[pair[0]], invconnections[pair[1]]
				invconnections[pair[0]], invconnections[pair[1]] = p1, p0
				connections[p0],connections[p1] = pair[1], pair[0]
				result += pair
				#print()
				break
			elif (p_carry, 'XOR', xy_sum) not in connections and (xy_sum, 'XOR', p_carry) not in connections:
				#print('UNFOUND!')
				pair = list({invconnections[f'z{i:02}'][0], invconnections[f'z{i:02}'][2]} ^ {xy_sum, p_carry})
				#print(pair)
				p0,p1 = invconnections[pair[0]], invconnections[pair[1]]
				invconnections[pair[0]], invconnections[pair[1]] = p1, p0
				connections[p0],connections[p1] = pair[1], pair[0]
				result += pair
				#print()
				break
			#print()
			
			#print(f'pxy_carry = xy_sum & p_carry', (xy_sum, 'AND', p_carry))
			if (xy_sum, 'AND', p_carry) in connections:
				pxy_carry = connections[(xy_sum, 'AND', p_carry)]
			elif (p_carry, 'AND', xy_sum) in connections:
				pxy_carry = connections[(p_carry, 'AND', xy_sum)]
			else:
				print('UNFOUND')
				return
			#print('pxy_carry:', xy_carry)
			#print()
			
			#print(f'carry = xy_carry | pxy_carry', (xy_carry, 'OR', pxy_carry))
			if (xy_carry, 'OR', pxy_carry) in connections:
				p_carry = connections[(xy_carry, 'OR', pxy_carry)]
			elif (pxy_carry, 'OR', xy_carry) in connections:
				p_carry = connections[(pxy_carry, 'OR', xy_carry)]
			else:
				print('UNFOUND')
				return
			#print('new p_carry:', p_carry)
			#print()
			
	return ','.join(sorted(result))


if __name__ == "__main__":
	input_file = sys.argv[1] if len(sys.argv)>1 else 'input.txt'
	start = time.time()
	answer = solution(input_file)
	solution_time = time.time() - start
	print(f"- **Answer**: {answer}")
	print(f"- **Timing**: {solution_time}")

