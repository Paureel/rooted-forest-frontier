# Fixed mixed-overlap control amendment v2

Frozen after v1 plants/pilot, before this new literal is executed. New literal is hand-constructed from public source and selector definitions, not candidate-derived.

A=((0,2),1), B=(((3,4),7),((5,6),8)), C=(9,10), S=(A,(B,C)).
T=(((2,((0,1),((3,5),(4,6)))),(7,8)),(9,10)).
P=012|345678|9,10.
Expected actual selector edge(00,001), Ainside01/Aoutside2, Binside3456/Boutside78. A and B bad, C good and clear. A sectors both good; Binside rooted-bad.

Literal splitA budget3 output (ordered):
partition [[3,4,7,5,6,8],[0,1],[2],[9,10]], cuts [10,0,001].
Literal splitB budget3 outputs empty. At budget4 exact ordered outputs:
1. partition [[5,6],[3,4],[9,10],[0,2,1],[7,8]], cuts [1010,1000,11,0].
2. partition [[8],[7],[9,10],[0,2,1],[3,4,5,6]], cuts [1011,1001,11,0].
Each has global source-cost4. In output1 the current Bforest includes source pieces56 and34 whose TARGET minimal hulls overlap inside the3456 sector. This raw occurrence MUST remain in full/retained ForestState controls. It is not a valid ordinary whole-parent target-disjoint query. The mixed raw cost vector is[3,4,4]; no candidate paid-trace prediction is inferred.

Cap amendment: this single fixed case enumerates 5*203*2=2030 source refiners. v1 S10 measured0.0145s for450 refiners; same representation linear projection0.0654s for2030, explicitly rough because block-size checks vary. Run one measured S11 pilot before the full transformed bank. No broad unmeasured search.

Fixed transformed bank: base ROOT8,S8,S9,S10,S11; variants identity, swap parent names A/B only, mirror both original trees at every node, mirror SOURCE only, and injective natural relabel x→17*x+101. These are five concrete variants,25 cases total; source-refiner denominator(50+50+150+450+2030)*5=13650. Selector addresses: mirror target flips every0/1 bit; source-only mirror does not alter selector; parent orientation leaves actual target choice unchanged. Labels are arbitrary nonconsecutive natural integers, consistent with public Nat model. Negative-label graph controls may be reported as representation tests only, outside the formal Nat input type.

Coverage at q5 must hold for every enumerated original AF; both-crossing target ownership must fail. Preserve all source output occurrences including internal overlap. For transformed cases, exact output list ordering is not imported from untransformed expectations; only base literals grade exact order. Permutations map mathematical properties, while a fresh base-source run grades order.
