
	for t, vs in entries:
		cache = dict()
		def rec(it,iv, t,vs,cache):
			if it == len(t):
				if iv == len(vs):
					return 1
				return 0
				
			# pass empties
			while t[it] == '.':
				it += 1
			# collect any hits
			hashsum = 0
			while t[it] == '#':
				it += 1
			if hashsum > vs[iv]:
				return 0
			if t[it] == '.' and hashsum < vs[iv]:
				return 0
			
			return rec(it+1,iv, t,vs,cache)
			if (it,iv) in cache:
				return cache[(it,iv)]
