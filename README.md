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

## 2021 Solutions
### Day 1: Sonar Sweep 
#### Part 1
- **Approach**: Simple iteration keeping track of the previous value.
- **Answer**: 1342
- **Timing**: 0.0011320114135742188
#### Part 2
- **Approach**: Simple iteration keeping track of the previous 3 values.
- **Answer**: 1378
- **Timing**: 0.0016851425170898438

### Day 2: Dive!
#### Part 1
- **Approach**: Simple iteration keeping track of the value.
- **Answer**: 1568138742
- **Timing**: 0.002246856689453125
#### Part 2
- **Approach**: Simple iteration keeping track of the values.
- **Answer**: 1568138742
- **Timing**: 0.0033369064331054688

### Day 3: Binary Diagnostic
#### Part 1
- **Approach**: Taking counts and checking if they were the majority.
- **Answer**: 1540244
- **Timing**: 0.002835988998413086
#### Part 2
- **Approach**: Solved using numpy's summation along a chosen axis, plus numpy's masking, plus binary conversion.
- **Answer**: 4203981
- **Timing**: 0.008578062057495117

### Day 4: Giant Squid
#### Part 1
- **Approach**: Used Numpy. Keep track of masks of called numbers. Use axial summations to check for solutions.
- **Answer**: 10680
- **Timing**: 0.06001400947570801
#### Part 2
- **Approach**: Same as part 1, just kept track of which puzzles hadn't been solved yet.
- **Answer**: 31892
- **Timing**: 0.32416582107543945

### Day 5: Hydrothermal Venture
#### Part 1
- **Approach**: Solved by actually constructing the grid and using numpy's indexing to update it.
- **Answer**: 6283
- **Timing**: 0.017503976821899414
#### Part 2
- **Approach**: Solved by actually constructing the grid and walking along it.
- **Answer**: 18864
- **Timing**: 0.34270477294921875

### Day 6: Lanternfish
#### Part 1
- **Approach**: Solved by simply simulating the fish reproduction.
- **Answer**: 354564
- **Timing**: 0.9740469455718994
#### Part 2
- **Approach**: Solved using dynamic programming with memoization.
- **Answer**: 1609058859115
- **Timing**: 0.004016876220703125

### Day 7: 
#### Part 1
- **Approach**: Solved using hill climbing starting from the mean.
- **Answer**: 329389
- **Timing**: 0.07007932662963867
#### Part 2
- **Approach**: Solved using the same approach as the first part, but with the formulat to compute triangular numbers.
- **Answer**: 86397080
- **Timing**: 0.0022478103637695312

### Day 8: Seven Segment Search 
#### Part 1
- **Approach**: Solved by simply comparing lengths.
- **Answer**: 479
- **Timing**: 0.0046727657318115234
#### Part 2
- **Approach**: Ended up just using brute force since the 7 segments means 7!=5040 possibilities for each entry.
- **Answer**: 1041746
- **Timing**: 10.353924989700317

### Day 9: Smoke Basin
#### Part 1
- **Approach**: Solved by simply iterating over the array and checking neighbors.
- **Answer**: 633
- **Timing**: 0.03409886360168457
#### Part 2
- **Approach**: Solved using skimage's food function. Mathematical morphology functions are often useful for topograpical data.
- **Answer**: 1050192
- **Timing**: 0.14930510520935059

### Day 10: Syntax Scoring
#### Part 1
- **Approach**: Solved using a stack to store opening brackets.
- **Answer**: 341823
- **Timing**: 0.002851247787475586
#### Part 2
- **Approach**: Same approach as the first part, small tweak.
- **Answer**: 2801302861
- **Timing**: 0.003412008285522461

### Day 11: Dumbo Octopus
#### Part 1
- **Approach**: Solved using a mask to find new flashes, and convolving to find the effect of the flash. Repeat on each step to get fixed points.
- **Answer**: 1661
- **Timing**: 0.691169023513794
#### Part 2
- **Approach**: Same as part 1, just letting it run until the synchronize step is found.
- **Answer**: 334
- **Timing**: 2.2901859283447266

### Day 12: Passage Pathing
#### Part 1
- **Approach**: Solved using depth-first search.
- **Answer**: 5920
- **Timing**: 0.7616209983825684
#### Part 2
- **Approach**: Solved using depth-first search, keeping the ability to revisit nodes as a boolean flag.
- **Answer**: 155477
- **Timing**: 23.019680976867676

### Day 13: Transparent Origami
#### Part 1
- **Approach**: Reflected all coordinates over the folds and used a set for uniqueness.
- **Answer**: 708
- **Timing**: 0.01527714729309082
#### Part 2
- **Approach**: Same as day 1, but had to add a function to print the final result.
- **Answer**: EBLUBRFH
- **Timing**: 0.044972896575927734

### Day 14: Extended Polymerization
#### Part 1
- **Approach**: Direct simulation by looping over the string and appending to a new string.
- **Answer**: 2703
- **Timing**: 0.019144058227539062
#### Part 2
- **Approach**: Solved by keeping track of pair frequency counts.
- **Answer**: 2984946368465
- **Timing**: 0.004538297653198242

### Day 15: Chiton
#### Part 1
- **Approach**: Used NetworkX to perform Dijkstra. Graph was a digraph where edge weight was the cost of entering a node.
- **Answer**: 811
- **Timing**: 0.39791393280029297
#### Part 2
- **Approach**: Same as part 1. Used numpy's tile and indexing to do the size-up of the cave, with some modular arithmetic.
- **Answer**: 3012
- **Timing**: 25.534971952438354

### Day 16: Packet Decoder
#### Part 1
- **Approach**: Basically perform the whole package parsing using lots of binary and hex conversion and string operations.
- **Answer**: 891
- **Timing**: 0.002791166305541992
#### Part 2
- **Approach**: Same as part one, but added an operator evaluation.
- **Answer**: 673042777597
- **Timing**: 0.0028810501098632812

### Day 17: Trick Shot
#### Part 1
- **Approach**: Brute force searched all reasonable starting values for the max.
- **Answer**: 5050
- **Timing**: 11.546349048614502
#### Part 2
- **Approach**: Brute forced by searching in a reasonable radius of all starting values that hit the target.
- **Answer**: 2223
- **Timing**: 491.1251199245453

### Day 18: Snailfish
#### Part 1
- **Approach**: Used a string/linked-list based approach, which made getting the first left and right numbers easier.
- **Answer**: 3816
- **Timing**: 0.31192922592163086
#### Part 2
- **Approach**: Simply brute-force checked all pairs for the max value.
- **Answer**: 4819
- **Timing**: 5.628562927246094

### Day 19: Beacon Scanner
#### Part 1
- **Approach**: Construct the rotation matrices by permuting the x and y axes, then cross product to get z. Then iterate over all the remaining scanners, over rotations, and get possible translations by matching pairs of beacons to check if at least 12 match up.
- **Answer**: 318
- **Timing**: 510.60430884361267
#### Part 2
- **Approach**: Same as part 1, except saved time by recording pairs of fixed scanners already checked. Also saved the translations used as well, since that's the scanner's position. Check all pairs of scanners for max distance.
- **Answer**: 12166
- **Timing**: 288.3640456199646

### Day 20: Trench Map
#### Part 1
- **Approach**: Used numpy's padding to account for growth, and generic_filter to apply the transform, with the bounday values being fed to the filter and kept track of.
- **Answer**: 5249
- **Timing**: 0.6359641551971436
#### Part 2
- **Approach**: Same as part 1.
- **Answer**: 15714
- **Timing**: 64.92884492874146

### Day 21: Dirac Dice
#### Part 1
- **Approach**: Direct simulation using modular arithmetic and accounting for off-by-one.
- **Answer**: 1004670
- **Timing**: 0.001110076904296875
#### Part 2
- **Approach**: Dynamic programming with memoization, 5D statespace `(10*10*21*21*2)`. Construct all possible results of a turn and follow their game trees.
- **Answer**: 492043106122795
- **Timing**: 1.7679462432861328

### Day 22: Reactor Reboot
#### Part 1
- **Approach**: Solved using set operations to keep track of all the on-cubes, with xyz nested loops.
- **Answer**: 658691
- **Timing**: 1.0631992816925049
#### Part 2
- **Approach**: Find intersecting rectangular prisms, keep track of those whose volumes are added, and subtracted. Doesn't work on the second example, but works on the actual input?
- **Answer**: 1228699515783640
- **Timing**: 1.9604251384735107

### Day 23: Amphipod
#### Part 1
- **Approach**: Used A* with a bunch of processing to create the graph. States are stored as a tuple of positions, A* heuristic is cost to positions ignoring blocking. Valid moves are only to the hallway and back.
- **Answer**: 15160
- **Timing**: 2.1332180500030518
#### Part 2
- **Approach**: Same as part 1, except with the extra lines injected and augmented state space with a few small optimizations to avoid unnecessary moves.
- **Answer**: 46772
- **Timing**: 2703.6278762817383

### Day 24: Arithmetic Logic Unit
#### Part 1
- **Approach**: I found that the output wasn't particularly sensitive to input: random flip sets of digits, keeping records of the max found, hoping to break out of local maxima into a global maxima.
- **Answer**: 99429795993929
- **Timing**: 334.2366089820862
#### Part 2
- **Approach**: Same as part 1, just flipping the signs to get the minima.
- **Answer**: 18113181571611
- **Timing**: 330.92746686935425

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

### Day 20: Jurassic Jigsaw
#### Part 1
- **Approach**: Use edge-matching to construct a graph. The nodes with 2-edges only are corners.
- **Answer**: 8425574315321
- **Timing**: 7.094567060470581
#### Part 2
- **Approach**: Fix the orientation of one corner. Build up the rest of the puzzle from there. Then search using the convolution trick.

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

### Day 24: Lobby Layout
#### Part 1
- **Approach**: Hexagonal grid system, and sets.
- **Answer**: 394
- **Timing**: 0.007922172546386719
#### Part 2
- **Approach**: Hexagonal grid system, with some set logic (difference and union).
- **Answer**: 4036
- **Timing**: 3.2977421283721924

### Day 25: Combo Breaker
#### Part 1
- **Approach**: Brute force a Diffie-Helman key.
- **Answer**: 297257
- **Timing**: 6.192662000656128
#### Part 2
- **Approach**: Click a link.
