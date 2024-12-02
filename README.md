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

## 2024 Solutions
### Day 1: Historian Hysteria
#### Part 1
- **Approach**: Solved using split, and numpy for the the array sorting, differencing, absolute valueing and summing. 
- **Answer**: 2031679
- **Timing**: 0.0013058185577392578
#### Part 2
- **Approach**: Solved with similar parsing to part 1, Counter for the counts, and list comprehension with sum to finish off.
- **Answer**: 19678534
- **Timing**: 0.0015769004821777344

## 2023 Solutions
### Day 1: Trebuchet?!
#### Part 1
- **Approach**: Solved by just filtering the string with list comprehension.
- **Answer**: 55029
- **Timing**: 0.0026428699493408203
#### Part 2
- **Approach**: Solved by constructing the list of digits written out, and building up the line string, checking if they end with a digit or digit string.
- **Answer**: 55686
- **Timing**: 0.01918172836303711

### Day 2: Cube Conundrum
#### Part 1
- **Approach**: Solved by parsing using split, then used a mapping of maximum values and ensured every entry remained under.
- **Answer**: 2169
- **Timing**: 0.0012331008911132812
#### Part 2
- **Approach**: Solved parsing with splitting then keeping track of the maximum values of each color seen in each entry.
- **Answer**: 60948
- **Timing**: 0.0014262199401855469

### Day 3: Gear Ratios
#### Part 1
- **Approach**: Solved by scanning by iterating over rows then cols, building up numbers found, and for each position scanning for adjacent symbols, then adding once end of number is found.
- **Answer**: 537832
- **Timing**: 0.00596928596496582
#### Part 2
- **Approach**: Similar to part 1, except keep track of all gears by their positions, and during scans over a number keep a set of all adjacent gears, at boundary add to that gear's list of ratios, which can then be accumulated at the end.
- **Answer**: 81939900
- **Timing**: 0.0064849853515625

### Day 4: Scratchcards
#### Part 1
- **Approach**: Solved using set intersection, and power of 2. Parsing done with splitting.
- **Answer**: 23673
- **Timing**: 0.0021820068359375
#### Part 2
- **Approach**: Similar to part 2, but kept track of the number of compies of each ticket, and performed the addition forward for each win, summing total at the end.
- **Answer**: 12263631
- **Timing**: 0.001964092254638672

### Day 5: If You Give A Seed A Fertilizer
#### Part 1
- **Approach**: Solved by parsing up the mappings, then for each seed going through each range to see if any can update the value.
- **Answer**: 51580674
- **Timing**: 0.000453948974609375
#### Part 2
- **Approach**: Solved by keeping track of ranges, and checking for range intersection, then cutting up the ranges as needed, and keeping the seeds in a stack in case they get cut into multiple ranges.
- **Answer**: 99751240
- **Timing**: 0.001138925552368164

### Day 6: Wait For It
#### Part 1
- **Approach**: Solved by simply running through each possible speed and checking if it wins. A more elegant solution using math is explained in part 2.
- **Answer**: 1710720
- **Timing**: 0.00019216537475585938
#### Part 2
- **Approach**: I solved it by filtering the spaces and letting the same code as part 1 run for a little longer. The instant solution is `math.ceil(math.sqrt(t**2 - 4 * d))`.
- **Answer**: 35349468
- **Timing**: 4.878834962844849

### Day 7: Camel Cards
#### Part 1
- **Approach**: Mapped face cards to apropriate ints, then used the `Counter` class to check for the hand's type, then set that up with the hand values and the bids after so they can be sorted, and then the final value computed.
- **Answer**: 253313241
- **Timing**: 0.004082918167114258
#### Part 2
- **Approach**: Similar to part 2, just updated the `Counter` logic to be cleaner, and for the wild-cards its always advantageous to match the most common already in hand (avoiding more Js). Realized should added in case of ties to use highest, but funny enough it still worked.
- **Answer**: 253362743
- **Timing**: 0.004853963851928711

### Day 8: Haunted Wasteland
#### Part 1
- **Approach**: We simply perform the simulation until the destination is reached.
- **Answer**: 20777
- **Timing**: 0.0029268264770507812
#### Part 2
- **Approach**: First found the cycles and their leads, noticing we need to keep track of which step in the instructions we're on as part of the state. Afterwards notice that target nodes only show up once per cycle and never in the leads. This means solving a system of congruences, with the Chinese Remainder Theorem, since they were all coprime up to the length of the instructionset: the input was generated for this convenience. For some reason Sympy's conguence solver didn't work, but the CRT did the trick. z3 will also solve this problem cleanly.
- **Answer**: 13289612809129
- **Timing**: 0.08982133865356445

### Day 9: Mirage Maintenance
#### Part 1
- **Approach**: Solved by directly doing the repeated difference, keeping track of the last values to sum them. Better solution is to know that this means we have a polynomial, and use an Lagrange polynomial fit.
- **Answer**: 2101499000
- **Timing**: 0.020541906356811523
#### Part 2
- **Approach**: Similar to part one, but directly simulated the subtracting at the beginning.
- **Answer**: 1089
- **Timing**: 0.020593881607055664

### Day 10: Pipe Maze
#### Part 1
- **Approach**: Solved by checking valid ajacencies, and then performing BFS on that.
- **Answer**: 6738
- **Timing**: 0.014072895050048828
#### Part 2
- **Approach**: Ended up using the Shapely library to check for polygon containing points. Had to do a traversal around the polygon to get all the points in the correct order. Tried implementing a winding-number solution but it didn't work.
- **Answer**: 579
- **Timing**: 17.63448190689087

### Day 11: Cosmic Expansion
#### Part 1
- **Approach**: Solved by simply performing the array expansion as we check each row and column for empties, then summing every pairwise distance.
- **Answer**: 10313550
- **Timing**: 0.017802953720092773
#### Part 2
- **Approach**: Just kept track of rows and columns which would be expanded, and when computing the distances for each pair, check of any rows or columns between them are in the expanded sets, and if so add on the additional distances.
- **Answer**: 611998089572
- **Timing**: 0.3986222743988037

### Day 12: Hot Springs
#### Part 1
- **Approach**: Solved using dynamic programming over the position along the template string, the number of matched streaks, and the current number of contiguous damaged springs.
- **Answer**: 7792
- **Timing**: 0.04003095626831055
#### Part 2
- **Approach**: Same dynamic programming as part 1, just increasing the input size as directed.
- **Answer**: 13012052341533
- **Timing**: 1.2259790897369385

### Day 13: Point of Incidence
#### Part 1
- **Approach**: Used numpy with indexing to compare vertical and horizontal mirrors about different candidate lines, being careful for bounds.
- **Answer**: 36041
- **Timing**: 0.016080141067504883
#### Part 2
- **Approach**: Similar to part 1, but just brute-force ran through all the possible flips in each array, checking we don't have original solution.
- **Answer**: 35915
- **Timing**: 0.9191727638244629

### Day 14: Parabolic Reflector Dish
#### Part 1
- **Approach**: Iterated over each column, going down the column, and keeping a queue of available places for the rounded rocks to fall, which is reset if we hit a stationary cube rock. After this summing the distances is easy.
- **Answer**: 105249
- **Timing**: 0.002225160598754883
#### Part 2
- **Approach**: The solution is to find the cycle, and compute the number of the remaining and subtract them out, so we only have the remainder of the cycle left. Used a hash on the ordered tuple of all rock positions to quick lookups.
- **Answer**: 88680
- **Timing**: 1.098949909210205

### Day 15: Lens Library
#### Part 1
- **Approach**: Solved by simply iterating through the string, and applying the operations, using Python's ord to get the ASCII values.
- **Answer**: 514394
- **Timing**: 0.002474069595336914
#### Part 2
- **Approach**: This was the perfect opportunity to use Python's OrderedDict class.
- **Answer**: 236358
- **Timing**: 0.0035469532012939453

### Day 16: The Floor Will Be Lava
#### Part 1
- **Approach**: Simply perform the simulation, keeping track of each beam head's position and direction to update accordingly. Keep track states visited to avoid loops, and keep track of tiles visited for the final answer.
- **Answer**: 8901
- **Timing**: 0.01546478271484375
#### Part 2
- **Approach**: Same as part 1, just brute-forced over each possible starting position.
- **Answer**: 9064
- **Timing**: 2.5953688621520996

### Day 17: Clumsy Crucible
#### Part 1
- **Approach**: Implemented Dijkstra's algorithm, using Python's heapq, also the state inclduded the direction and a countdown for steps taken in the same direction.
- **Answer**: 1039
- **Timing**: 0.4458200931549072
#### Part 2
- **Approach**: Same as part 1, but made it a count-up instead of down, and used that to filter states.
- **Answer**: 1201
- **Timing**: 1.6011888980865479

### Day 18: Lavaduct Lagoon
#### Part 1
- **Approach**: Made of a set of all dug points from the instructions, then bound the bounds and applied flood-fill on the boundary to find the complement area, and compute the final area.
- **Answer**: 38188
- **Timing**: 0.06021308898925781
#### Part 2
- **Approach**: This time used Shapely to do the geometry computations. Each instruction is a rectangle, so union them all, take the exterior polygon's area.
- **Answer**: 93325849869340
- **Timing**: 0.049382925033569336

### Day 19: Aplenty
#### Part 1
- **Approach**: Solved by simply implementing the instructions, using a dict for the workflows.
- **Answer**: 432427
- **Timing**: 0.002557992935180664
#### Part 2
- **Approach**: Keep track of ranges which are split as each rules is applied to them. When a range is accepted we can easily compute the number of elements within.
- **Answer**: 143760172569135
- **Timing**: 0.004436969757080078

### Day 20: Pulse Propagation
#### Part 1
- **Approach**: Simply perform the simulation by creating mappings of child parent relations, and flip-flop states and conjunction inputs, using a queue for the pulses, keeping track of value, destination and origin.
- **Answer**: 787056720
- **Timing**: 0.02446722984313965
#### Part 2
- **Approach**: In general since we have flip-flops with feedback, it's undecidable if a given circuit would even terminate running, let alone compute the number of presses: ie the problem is incomputable in general. However by assuming the input is crafted to terminate quickly, the number of possible states is 2 to the power of the flip-flops, which therefore must cycle eventually (again using the "always terminates" assumption). However by graphing the input with GraphViz we see 4 disjoint structures all feeding into the final rx, each with a tractable number of states: we can just find the cycle length for those, and then find the LCM, which works.
- **Answer**: 212986464842911
- **Timing**: 0.09630417823791504

### Day 21: Step Counter
#### Part 1
- **Approach**: Simply perform the simulation with BFS. Convolution is another possible approach.
- **Answer**: 3737
- **Timing**: 0.0711827278137207
#### Part 2
- **Approach**: Because of the repeating tile structure and Manhattan distance traversal, we eventually reach a point where the expanding diamond's edges will be the same along a side, and an increase of steps by a tile length will just add more tiles to the interior without changing the repeated structure of the edges. For the input we also have an "air gap" which makes it converge faster. Since the "area" covered will be proportional to the square of the distance, we can fit a quadratic and extrapolate. We take samples starting from the remainder with the target, then at every period equal to a tile length, and check for the point at which the 3rd difference is 0, indicating we have reached the polynomial regularity. Use a Lagrange polynomial for an exact fit.
- **Answer**: 625382480005896
- **Timing**: 37.46765995025635

### Day 22: Sand Slabs
#### Part 1
- **Approach**: We can determine the pile up without simulating, just by checking which blocks below a given block intersect with it in the xy. By sorting by lowest z value we ensure we process in the right order and get a final a value for each block. For each block we need to check which blocks it could land on and place it 1 space above the max possible final z. We can use the same xy intersection and comparison of final z position to find which blocks are on top of which other. A block with only 1 support means that support can't be disintegrated, so we can count up the essential blocks.
- **Answer**: 395
- **Timing**: 0.6963539123535156
#### Part 2
- **Approach**: Similar computation of block order as part 1, but inverting the mapping of blocks into others gives which blocks a given block supports. For each block we need to search for which blocks will fall if removed in order: use a heap as a priority queue by max z height, so as to ensure we process all supports of a given block before the block itself to see if it falls.
- **Answer**: 64714
- **Timing**: 1.1418240070343018

### Day 23: A Long Walk
#### Part 1
- **Approach**: The hint about going downhill implies there will be no possible loops. So we can give an id to each branch we are exploring, updated at each junction we reach: we cannot go to a node with the same id, or back onto a predecessor, since that would be backtracking. Otherwise we're just trying to find the longest route possible by updating a mapping of longest distances to get to a given node found so far with a typical graph traversal.
- **Answer**: 2166
- **Timing**: 0.060801029205322266
#### Part 2
- **Approach**: Run through the grid identifying junctions, then search from each junction to find neighboring junctions and the distance to them, thus construct the simplified weighted graph. Use dynamic programming to find the simple path of maximum total distance.
- **Answer**: 6378
- **Timing**: 37.93946313858032

### Day 24: Never Tell Me The Odds
#### Part 1
- **Approach**: Just iterated over all pairs and did the algebra to find the intersections, checking if parallel first. Use algebra as well to make sure the time of the intersecctions is positive. Then just count all intersections that fall in the bounds.
- **Answer**: 31921
- **Timing**: 0.046591997146606445
#### Part 2
- **Approach**: Solved by throwing the large system of non-linear integer equations into z3. Had to remove the time variables with algebra, so we only had 6 variables in the end for each initial position and velocity components. Without z3 could have constructed a Lagrangian with the sum of squares of each equation and solved numerically.
- **Answer**: 761691907059631
- **Timing**: 0.8538029193878174
- **Note**: First time leaderboarding at 35th place on pt 2!

### Day 25: Snowverload
#### Part 1
- **Approach**: Solved using NetworkX to find the minimum cut, and the itertools library to go over each combination of start and end pairs for the flow, checking each one if the cut value was 3 edges, and the partition was size 2.
- **Answer**: 572000
- **Timing**: 0.053193092346191406
#### Part 2
- **Approach**: Click a link.

## 2022 Solutions
### Day 1: Calorie Counting
#### Part 1
- **Approach**: Sum the sub-lists then take the max.
- **Answer**: 70613
- **Timing**: 0.0005538463592529297
#### Part 2
- **Approach**: Sum the sub-lists then sort and sum the top 3.
- **Answer**: 205805
- **Timing**: 0.0008478164672851562

### Day 2: Rock Paper Scissors
#### Part 1
- **Approach**: Constructed the map of points from each case, and a if-switch for the shape-points.
- **Answer**: 11873
- **Timing**: 0.0019898414611816406
#### Part 2
- **Approach**: Constructed an inverse of the points map to determine which symbol was needed, then proceeded with the original points calculation.
- **Answer**: 12014
- **Timing**: 0.002454996109008789

### Day 3: Rucksack Reorganization
#### Part 1
- **Approach**: Solved by slicing each string in half, then taking the intersection of the sets of each half, and finally performing ordinal arithmetic on the resulting character.
- **Answer**: 7742
- **Timing**: 0.0009257793426513672
#### Part 2
- **Approach**: Solved by going 3 at a time, and taking the set intersection between all, finishing with the same ordinal arithmatic.
- **Answer**: 2276
- **Timing**: 0.0005550384521484375

### Day 4: Camp Cleanup
#### Part 1
- **Approach**: Solved by simply checking each range to see if it contained the other.
- **Answer**: 509
- **Timing**: 0.002546072006225586
#### Part 2
- **Approach**: Solved using the classic range intersection formula: to intersect the smallest of each must be less than the largest of the opposite.
- **Answer**: 870
- **Timing**: 0.002237081527709961

### Day 5: Supply Stack
#### Part 1
- **Approach**: Solved by directly simulating the stack moving, popping one element at a time. Mostly was tricky parsing the data, did so by counting spacing between chars.
- **Answer**: TBVFVDZPN
- **Timing**: 0.000982046127319336
#### Part 2
- **Approach**: Solved by directly simulating the stacks, this time with array slicing.
- **Answer**: VLCWHTDSZ
- **Timing**: 0.0006537437438964844

### Day 6: Tuning Trouble
#### Part 1
- **Approach**: Solved using sets to check for uniqueness in the rolling window.
- **Answer**: 1140
- **Timing**: 0.0010941028594970703
#### Part 2
- **Approach**: Same as part 1.
- **Answer**: 3495
- **Timing**: 0.006528139114379883

### Day 7: No Space Left On Device
#### Part 1
- **Approach**: Solved by creating the file-system tree with dicts, including the parent link, and recursive tree traversal to compute the directory sizes and final result.
- **Answer**: 1307902
- **Timing**: 0.0007040500640869141
#### Part 2
- **Approach**: Same as part 1, but with less to compute, and using a global dict of directory sizes to finally run through to find the optimal directory to delete.
- **Answer**: 7068748
- **Timing**: 0.0007309913635253906

### Day 8: Treetop Tree House
#### Part 1
- **Approach**: Simply performed the looping on each element for each direction. Careful of off-by-one errors!
- **Answer**: 1560
- **Timing**: 0.023669004440307617
#### Part 2
- **Approach**: Simply performed the looping on each element for each direction. Careful of off-by-one errors!
- **Answer**: 252000
- **Timing**: 0.044738054275512695

### Day 9: Rope Bridge
#### Part 1
- **Approach**: Solved creating the map of all moves needed. Also not a move is only needed if the difference in one dimension is greater than 1. Also count coordinates in a set.
- **Answer**: 6037
- **Timing**: 0.013653993606567383
#### Part 2
- **Approach**: Similar to part 1, but adding the extra possible "full diagonal" moves and keeping track of the full list of knots and updating with a prev.
- **Answer**: 2485
- **Timing**: 0.07366514205932617

### Day 10: Cathode-Ray Tube
#### Part 1
- **Approach**: Solved using modular arithmetic to check when at the correct instruction, and fully simulating every cycle.
- **Answer**: 12980
- **Timing**: 0.00016617774963378906
#### Part 2
- **Approach**: Solved by using modular arithmetic, and indexing into the resulting image.
- **Answer**: BRJLFULP
- **Timing**: 0.0001888275146484375

### Day 11: Monkey in the Middle
#### Part 1
- **Approach**: Implement each monkey as a dictionary of it's features, then loop through the rounds over each monkey's items computing the new worry and new monkey. Use Python's deque for the items queue. A list to keep track of how many items each monkey inspects can then be sorted to find the top 2.
- **Answer**: 121450
- **Timing**: 0.0008020401000976562
#### Part 2
- **Approach**: Same as part 1, but the worry to explode taking up a lot of memory and computational time: we only need the divisibility as a test, and that won't change if we work with the modulus of a number that is divisible by all divisibility tests.
- **Answer**: 28244037010
- **Timing**: 0.3814840316772461

### Day 12: Hill Climbing Algorithm
#### Part 1
- **Approach**: Solved using NetworkX to implement the shortest path algorithm. All I had to do was contruct the directed graph by parsing the grid with ord and checking valid neighbors.
- **Answer**: 394
- **Timing**: 0.03999900817871094
#### Part 2
- **Approach**: Same as part one, but searched for all starting points and iterated over them to get the best result. Had to use try/except for NetworkX's NetworkXNoPath error.
- **Answer**: 388
- **Timing**: 1.6430201530456543

### Day 13: Distress Signal
#### Part 1
- **Approach**: Solved by implementing the comparator as described. Use the json library to parse the lists.
- **Answer**: 6420
- **Timing**: 0.002544879913330078
#### Part 2
- **Approach**: Same as part 1, except removing double-newlines, adding in the extra packets for separators. Used functools.cmp_to_key to turn the comparator into a sort key.
- **Answer**: 22000
- **Timing**: 0.0056760311126708984

### Day 14: Regolith Reservoir
#### Part 1
- **Approach**: Solved using numpy for the grid and simulating each grain at a time.
- **Answer**: 1298
- **Timing**: 0.08171701431274414
#### Part 2
- **Approach**: Same as part 1, but widening for more sand dropping, and including the floor bound.
- **Answer**: 25585
- **Timing**: 2.062486171722412

### Day 15: Beacon Exclusion Zone
#### Part 1
- **Approach**: Solved using a set of all indices found on the y line, which is filled by started at the nearest point on the y, and moving while within the distance and adding. Finish by removing all actual beacons from the set.
- **Answer**: 5508234
- **Timing**: 2.092556953430176
#### Part 2
- **Approach**: Solved by looking at the perimeters just outside of each sensor, for each point checking the distances with every other beacon and stopping once a valid solution is found. This turns the 2D problem into a 1D problem.
- **Answer**: 10457634860779
- **Timing**: 345.6069059371948

### Day 16: Proboscidea Volcanium
#### Part 1
- **Approach**: Solved by first using NetworkX to find the distances between all pairs of tunnels. It is now a problem of finding the optimal ordering of the valves to open. Then the key insight to making the problem computationally feasible is to notice that most of the valves have a flow-rate of 0 and can be ignored. Perform a DFS keeping track of the current location, the time and the state of the valves.
- **Answer**: 2253
- **Timing**: 1.5662117004394531
#### Part 2
- **Approach**: Similar to part 1, but using the insight that the valves you and the elephant visit will be independent, and so we can run the same BFS on masks and complements of all non-zero valves and take the sum. Caching by current valve, time remaining and valve states, makes this go much faster.
- **Answer**: 2838
- **Timing**: 100.70373129844666

### Day 17: Pyroclastic Flow
#### Part 1
- **Approach**: Solved by simply simulating the falling, and keeping track of the max height. Filled positions are kept in a set for quick checking for collisions.
- **Answer**: 3100
- **Timing**: 0.05015397071838379
#### Part 2
- **Approach**: Solved using part 1 for the simulation, then looking for a cycle where the position in the jet pattern is the same, and the last block dropped is the same and the filled positions are the same. That way we can find the rounds of the cycle remaining and the height difference from each cycle and simply multiply through instead of simulating, finishing off with the remainder heigh difference. I used the last positions of the complete set of blocks as the resting position hash, which worked for this puzzle input.
- **Answer**: 1540634005751
- **Timing**: 0.04747128486633301

### Day 18: Boiling Boulders
#### Part 1
- **Approach**: Solved using a set of all the faces found and all the faces found more than once. The hash key for the face are the block coordinates on either side of the face in sorted order.
- **Answer**: 3576
- **Timing**: 0.012495040893554688
#### Part 2
- **Approach**: Solved by first performing a flood-fill via BFS on each block and seeing if doesn't escape. Keeping record of which blocks have already been searched.
- **Answer**: 2066
- **Timing**: 0.033136844635009766

### Day 19: Not Enough Minerals
#### Part 1
- **Approach**: Essentially a DFS/DP search for the optimal building choices at each time step for each blueprint. Optimizations include not needing to represent the number of geodes or geode bots in the state (we can compute their contribution on the spot), always choose to build a geode bot when possible, and finally don't continue to build bots after we are producing more than we could possibly spend in a given time-step. Also careful to only update resources after construction choice is made, but before the robot is added.
- **Answer**: 978
- **Timing**: 151.48627495765686
#### Part 2
- **Approach**: I ended up finding that the fastest way for me to solve this one was to just wait the extra time for the longer depth search to run. Optimizations from part 1 apply to part 2 as well.
- **Answer**: 15939
- **Timing**: 345.3918488025665

### Day 20: Grove Positioning System
#### Part 1
- **Approach**: The main trick is to keep track of the original indices of each number in another list an apply the transformations to each. Use the index, pop and insert list operations and modular arithmetic. Be careful with the off-by-one errors.
- **Answer**: 11073
- **Timing**: 0.11217880249023438
#### Part 2
- **Approach**: Same as part 1, but applying the extra transformations keeping track of the very original positions. Extra care with the modular arithmetic.
- **Answer**: 11102539613040
- **Timing**: 1.6746490001678467

### Day 21: Monkey Math
#### Part 1
- **Approach**: Simply ran through the process of elimination until the root was found.
- **Answer**: 232974643455000
- **Timing**: 0.003342151641845703
#### Part 2
- **Approach**: This problem was perfect for z3. Simply parse out all the relations, and ensure 'humn' is left as a free variable. One pitfall was to make sure to enforce divisions are only allowed when there aren't remainders.
- **Answer**: 3740214169961
- **Timing**: 2.268770694732666

### Day 22: Monkey Map
#### Part 1
- **Approach**: Keep track of the orientation, and have a map for changing the orientation. Walking off edges can be handled with modular arithmetic and not counting steps on empty spots, evaluating the actual step forward lazily in case of a wall.
- **Answer**: 103224
- **Timing**: 0.03242206573486328
#### Part 2
- **Approach**: After sketching the net on a piece of paper I realized we could use my same approach as part 1 if we also mark some of the empty tiles to "mirror/bounce" the orientation to go around corners. It ended up working very elegantly.
- **Answer**: 189097
- **Timing**: 0.049916982650756836

### Day 23: Unstable Diffusion
#### Part 1
- **Approach**: Fairly straighforward implementation of the instructions. There were several gotchas, such as the elves no longer moving as soon as they have no neighbors. Performed the simulation with loops, including some cleverness to cycle through the order of direction proposals. Also padded only when needed, and did a final shaving before reporting the final answer.
- **Answer**: 4158
- **Timing**: 0.377399206161499
#### Part 2
- **Approach**: Same as part 1, but letting the loop continue until the counts of proposed positions turned up 0.
- **Answer**: 1014
- **Timing**: 37.766417264938354

### Day 24: Blizzard Basin
#### Part 1
- **Approach**: Used a list of keep track of blizzard positions and orientations and updated with modular arithmetic. The paths are independently cyclic, so just find the common multiple which was relatively low, and run through all board configurations once. Construct the graph of positions and round keys, with the final exit as a special position without round, then find the shortest path with NetworkX.
- **Answer**: 334
- **Timing**: 2.791645050048828
#### Part 2
- **Approach**: Same as part 1, but just added a special state for the exiting at the beginning. Then solve there, back, and there again, using the distances to compute the round start of the next trip. Note it is always optimal to arrive as soon as possible then wait if need be.
- **Answer**: 934
- **Timing**: 3.043268918991089

### Day 25: Full of Hot Air
#### Part 1
- **Approach**: An exotic base system, easy enough do the interpretation into a number in memory, however as for how to get back, I just threw z3 at it since I knew it would solve it without fuss. Each digit is a variable with bounds.
- **Answer**: 2-=2-0=-0-=0200=--21
- **Timing**: 0.029268980026245117
#### Part 2
- **Approach**: Click a link.

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
- **Approach**: Solved using skimage's flood function. Mathematical morphology functions are often useful for topograpical data.
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

### Day 25: Sea Cucumber
#### Part 1
- **Approach**: Solved using Numpy and Scipy's generic filter.
- **Answer**: 329
- **Timing**: 29.969828844070435
#### Part 2
- **Approach**: Click a link.

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
