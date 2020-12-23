# AdventofCode
Solutions to the Advent of Code puzzles

https://adventofcode.com  

## About Advent of Code
https://www.reddit.com/r/adventofcode  
From their website's About page:  
Advent of Code is an Advent calendar of small programming puzzles for a variety of skill sets and skill levels that can be solved in any programming language you like. People use them as a speed contest, interview prep, company training, university coursework, practice problems, or to challenge each other.  

Advent of Code does not seems to have any restrictions on sharing solutions, and even seems to encourage it on Reddit.  
In the spirit of Project Euler's request to make solutions posting to be educational, I am providing approach explanations and linking resources useful links in the READMEs associated with each year I do.

## About These Solutions
- These are my original solutions written in Python 3.
- The intent was to solve these problems as quickly as possible: I frequently time myself.
- Comments are sparse and the intended approach is to be written quickly.
- Solution values, timing on my laptop, and a terse solution approach are given in the READMEs for each year.
- I'm also adding a series of useful links to topics useful to each problem at the end.
- On occasion I will consider different approaches to the problem: the one I end of using remains in the ```AoC[year]_day[day]_[part].py```, while the discarded/incomplete solution will be in another file.

## 2020 Solutions
### Day 1: Report Repair
#### Part 1
- **Approach**: Brute force: nested for-loops with indexing to avoid double-count. (Time-memory trade-off possible by using dicts)
- **Answer**: 744475
- **Timing**: 0.0012722015380859375
#### Part 2
- **Approach**: Brute force: nested for-loops with indexing to double-count.
- **Answer**: 70276940
- **Timing**: 0.10711288452148438

### Day 2: Password Philosophy
#### Part 1
- **Approach**: Brute force: using regex to parse and the string character count function.
- **Answer**: 477
- **Timing**: 0.0092010498046875
#### Part 2
- **Approach**: Brute force: using regex to parse and string indexing.
- **Answer**: 686
- **Timing**: 0.005084991455078125

### Day 3: Toboggan Trajectory
#### Part 1
- **Approach**: Brute force: A simple count with some 2-D indexing and modular arithmetic.
- **Answer**: 173
- **Timing**: 0.000782012939453125
#### Part 2
- **Approach**: Brute force: A simple count with some 2-D indexing and modular arithmetic.
- **Answer**: 4385176320
- **Timing**: 0.0015599727630615234

### Day 4: Passport Processing
#### Part 1
- **Approach**: Brute force: string contains all.
- **Answer**: 247
- **Timing**: 0.0006909370422363281
#### Part 2
- **Approach**: Brute force: a lot of regex parsing and conditions checking.
- **Answer**: 145
- **Timing**: 0.008143186569213867

### Day 5: Passport Processing
#### Part 1
- **Approach**: Binary encoding.
- **Answer**: 848
- **Timing**: 0.0045549869537353516
#### Part 2
- **Approach**: Binary encoding then set difference (using range).
- **Answer**: 682
- **Timing**: 0.005724906921386719

### Day 6: Custom Customs
#### Part 1
- **Approach**: Set sizes. (Strings turned to sets)
- **Answer**: 6335
- **Timing**: 0.001828908920288086
#### Part 2
- **Approach**: Set sizes. Set intersection. (String turned to sets)
- **Answer**: 3392
- **Timing**: 0.003625154495239258

### Day 7: Handy Haversacks
#### Part 1
- **Approach**: Set union until fixed point. Regex parsing.
- **Answer**: 296
- **Timing**: 0.1304619312286377
#### Part 2
- **Approach**: Dynamic programming by recording sub-solutions. Build graph.
- **Answer**: 9339
- **Timing**: 0.00913095474243164

### Day 8: Handheld Halting
#### Part 1
- **Approach**:
- **Answer**: 1134  
- **Timing**: 0.0004050731658935547  
#### Part 2
- **Approach**: 
- **Answer**: 1205  
- **Timing**: 0.04296088218688965  

### Day 9: Encoding Error
#### Part 1
- **Answer**: 556543474  
- **Timing**: 0.0531001091003418  
#### Part 2
- **Answer**: 76096372  
- **Timing**: 0.08516788482666016  

### Day 10: Adapter Array
#### Part 1
- **Approach**: Sort the array, then 1st difference, then count values.
- **Answer**: 2048
- **Timing**: 0.0002040863037109375
#### Part 2
- **Approach**: Sort the array, then use dynamic programming to solve: recursive solution with dictionary of memorized subsolutions.
- **Answer**: 1322306994176
- **Timing**: 0.0011546611785888672

### Day 11: Seating System
#### Part 1
- **Approach**: Brute force iterations, checking all neighbors, and checking for changes (fixed point). (Better solution would have been numpy convolutions, boolean operations, and sums)
- **Answer**: 2222
- **Timing**: 3.128587007522583
#### Part 2
- **Approach**: Similar to above, this time iterated over directions, and iterated up distance. (For this one the indexing would be better than convolution)
- **Answer**: 2032
- **Timing**: 9.079081058502197

### Day 12: Rain Risk
#### Part 1
- **Approach**: Brute force. Used trig functions for the angle of rotation.
- **Answer**: 1631
- **Timing**: 0.0032689571380615234
#### Part 2
- **Approach**: Brute force, with rotation matrix for rotations.
- **Answer**: 58606
- **Timing**: 0.003119945526123047

### Day 13: Shuttle Search
#### Part 1
- **Approach**: Modular arithmetic.
- **Answer**: 4722
- **Timing**: 0.00025200843811035156
#### Part 2
- **Approach**: Chinese Remainder Theorem.
- **Answer**: 825305207525452
- **Timing**: 0.0005371570587158203

### Day 14: Docking Data
#### Part 1
- **Approach**: Bitstring conversion and manipulation.
- **Answer**: 10035335144067
- **Timing**: 0.006556987762451172
#### Part 2
- **Approach**: Similar to above with binary counting.
- **Answer**: 3817372618036
- **Timing**: 0.9705009460449219

### Day 15: Rambunctious Recitation
#### Part 1
- **Approach**: Brute force with a dict.
- **Answer**: 421
- **Timing**: 0.0009579658508300781
#### Part 2
- **Approach**: Exact same.
- **Answer**: 436
- **Timing**: 20.582706928253174

### Day 16: Ticket Translation
#### Part 1
- **Approach**: Regex parsing. Check all bounds.
- **Answer**: 25916
- **Timing**: 0.10727190971374512
#### Part 2
- **Approach**: Keep sets of possibilities for each column. Cut down by bounds checks. Cut down final by filtering out fields of unique possibility remaining colums until fixed point.
- **Answer**: 2564529489989
- **Timing**: 0.20316219329833984

### Day 17: Conway Cubes
#### Part 1
- **Approach**: Multi-dimensional Conway's Game of Life. Used numpy's padding and convolution.
- **Answer**: 348
- **Timing**: 0.03930306434631348
#### Part 2
- **Approach**: Same answer as above, just updated the dimension.
- **Answer**: 2236
- **Timing**: 0.4158620834350586

### Day 18: Operation Order
#### Part 1
- **Approach**: Shunting-Yard algorithm to convert to RPN, and compute. Some tokenizing too.
- **Answer**: 3885386961962
- **Timing**: 0.018116235733032227
#### Part 2
- **Approach**: Same answer as above, just added operator precedence.
- **Answer**: 112899558798666
- **Timing**: 0.018545866012573242

### Day 19: Monster Messages
#### Part 1
- **Approach**: Parse rules into regex, then use to verify matches.
- **Answer**: 151
- **Timing**: 0.03327608108520508
#### Part 2
- **Approach**: Use same answer as above, but when self-loop is found use finite-depth recursion. (Solves the problem but isn't general)
- **Answer**: 386
- **Timing**: 1.9034090042114258

### Day 21: Allergen Assessment
#### Part 1
- **Approach**: Set logic: set intersection helps obtain possibilities for each alergen, set union gets all ingredients, then set difference gives all allergen-free.
- **Answer**: 1945
- **Timing**: 0.0016810894012451172
#### Part 2
- **Approach**: Cut out alergy-free set of all possibilities. Then use similar approach to day 16-2.
- **Answer**: pgnpx,srmsh,ksdgk,dskjpq,nvbrx,khqsk,zbkbgp,xzb
- **Timing**: 0.0012407302856445312

### Day 22: Crab Combat
#### Part 1
- **Approach**: Simple implementation of the rules with list functions.
- **Answer**: 35818
- **Timing**: 0.0005939006805419922
#### Part 2
- **Approach**: Recursion with list-slicing for copying.
- **Answer**: 34771
- **Timing**: 5.484330177307129

### Day 23: Crab Cups
#### Part 1
- **Approach**: Modular arithmetic.
- **Answer**: 82635947
- **Timing**: 0.0004520416259765625
#### Part 2
- **Approach**: Implemented a linked list, and used a dict.
- **Answer**: 157047826689
- **Timing**: 44.635998010635376
