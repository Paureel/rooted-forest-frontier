# Preproof controls, pinned 2026-10-15

No production graph theorem is present at this pin. All computations below are
DEVELOPMENT. The completed ordinary oracle and completed cherry source modules
are allowed contacts and cannot later certify this author independently.

Hand-constructed fixture family, with C containing a,b, and X the bad block:

- six: T=((((x,(a,b)),y),c),z), U=(((a,(x,(y,z))),c),b).
  Target cherry a,b; all actual cherries in both orientations have exactly two
  original pendants; neither orientation has Rule4. P=[X,{c},{a,b}]; X is bad;
  T[X] has exactly two outgoing incident arcs. This is Figure15.2. The literal
  branch 3(ii) cuts a,x,y, so costs are [2,1,3], not [2,1,2].
- third: X'=(w,(x,(p,q))), T=(c,(p,(x,(q,(w,(a,b)))))),
  U=(((a,X'),c),b). Same guards; Figure15.3, costs [2,1].
- first: with X' as above and V=(p,(x,(q,(w,c)))), T=(((a,b),V),s),
  U=((((a,X'),c),b),s). Same guards; Figure15.1, costs [2,1].
- common: use renamed copies V,W of the six pair. T=(V,((a,b),c)),
  U=(((a,W),c),b). Same guards; X has one incident incoming arc. This must
  produce an actual target/source split-edge witness, not a marked solver.
- two/large: use V,W as bad pendant; H=(p,q), respectively (r,(p,q));
  T=((p,V),(q,(a,b))) (enclose by r for large), U=((a,H),(b,W)).
  Same guards and exactly two homeomorphic blocks; ordinary cases 2 and 1.
- outside: T=((a,b),(q,(c,(p,V)))), U=((((a,W),c),b),(p,q)).
  Same guards, singleton other pendant, C has second cherry p,q; five cost2.

Negative plants, required before production proofs:

1. Missing priority: T=((a,b),(c,((x,y),z))), U=six.U. Local P is disjoint
   with exactly two good blocks, but global earlier-clear guard is false.
2. Outside clearance: T=((a,b),((y,s),(x,(z,c)))),
   U=((((a,(x,(y,z))),c),b),s). Target embeddings of literal P overlap.
3. Unpaid cuts: six literal Figure15.2 branch 3(ii) has three original cuts,
   three plus one nonempty residual components; claiming paid=2 must fail.
4. Strict refinement: first admits F={{a,c},{b},{w},{x},{p},{q},{s}},
   which neither has singleton a nor refines P. A safe branch therefore needs
   a no-larger exchange, not direct refinement of every original forest.

Comparator corruption: flip one expected admission to false and require named
rejection; clean twin must pass. Exact root addresses and costs will be emitted
by the executable record. Reversal/sibling-order and both input orientations
are checked by the same literal guards. No old census is run.

Pilot: one bounded fixture pass first; no fixture-pair census. Larger AF
enumeration is excluded until the pilot gives a measured rate.
