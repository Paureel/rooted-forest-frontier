# Qualified source cost

The source model counts visits to original tree constructors/vertices, original
edge endpoints, label-list entries, partition entries and returned labels, plus
Boolean/scalar operations and every list/string copy. A source restriction is
charged for its whole input walk and output construction; selecting and
materializing a literal forest is not a free operation. Returning a previous
forest pointer is not treated as constructing its final certificate.

Let n be the original leaf count, N=2n−1 the original vertices in one input,
L the largest encoded original label length, and B=1+bitlength(q). For the
integer Lean syntax use L=1+maximum original label bitlength. Label comparisons,
hashing, sorting keys and counters incur their actual encoded-size factor;
Python set/dict lookup can instead be conservatively implemented by linear
lists, multiplying all bounds below by O(NL+B). No average-case hash premise is
required for a polynomial bound.

The finite selector visits every original cherry and both endpoint orders,
checks no common cherry and both directions of the t1 rule, walks the original
paths for each relevant pair, and compares the c leaf with an actual source
cherry sibling. At most N ordered endpoint choices arise from actual cherries.
It scans actual source cherries to find c, computes the two original source
heads and all m original swapped heads, then materializes three literal source
partitions and their restricted trees. There is no set-partition or tree-pair
enumeration in selection. The source implementation materializes all admitted
choices before choosing the first; at most N choices occur because each chosen
a has only one original source cherry sibling. Charge every candidate, including
all discarded candidates and all three of each candidate's source states.

Conservatively, O(N^6 (L+B+1)^2) fine operations pay selection and all its
literal residual-graph walks, restrictions, copies and candidate sorting. This
is a qualified mathematical upper bound from loop lengths; no kernel theorem
in this package equates Python operations with that polynomial.

The conditional runner makes at most three callbacks. It charges all callback
request construction, budget tests and exact decrements. After each successful
callback it scans every returned block/label, compares rooted restrictions,
checks every original embedding and source-refinement relation, and records its
original cost identity. There are at most n blocks and n labels in any accepted
return. Even if each such check rescans the whole original tree, these checks
are bounded by the same conservative polynomial. Failure paths and rejected
child data are charged too; arbitrary malformed enormous child data is outside
the exact child IH and may be refused before full validation by size limits in
a production implementation. The printed IH bounds child data to original
partitions; it does not license trusting unbounded foreign data for the claimed
solver running time.

Minimum selection includes every successful returned label partition and its
copies. `solveForest` has the polynomial local toll described above. The
callback IH returns labelled partitions; it does not request final original
cut certificates from every child.

`solveCuts` then calls the actual completed formal `FinalCutRecovery.recover`
ONCE after minimum selection. That program uses the exact original-source
generator and has the completed conservative bound

    meterRecover(S,G).work <= finalPolynomial(S,G) * 2^(|G|-1)
                          <= finalPolynomial(S,G) * c^q   (c>=2).

Rule4Solve.solveCuts_recovery_work proves the second inequality from the actual
returned agreement and budget. The imported meterRecover_value theorem binds
the measured program to the literal recover call. This formal final recovery
is charged separately from the polynomial per-node label-selection toll; its
proved exponential bound is not silently called polynomial. The theorem
inherits the completed final-cut package's helper-to-fine-operation
qualification. Its direct scalar operations retain the label/counter bit
factors stated above.

The Python development runner instead extends disjoint original hulls by a
deterministic breadth-first walk and checks the full resulting residual graph.
That implementation has a polynomial reconstruction count, but this arm does
not claim a universal Lean/Python program-equivalence theorem. Both paths pay
one whole-original-source reconstruction and never union local child cuts.

The conditional label-selection recurrence therefore has a polynomial local
toll plus actual callbacks of costs 2,1,m>=2. For every rational c>=2 their
normalized LIST mass is at most c^(-1)+2c^(-2). A complete solver must account
for every local toll and for the final one-time c^q recovery term. For c=2,
the callback bound can be equality, so a q factor may accompany local tolls.
This arm does not supply the whole solver or its global work induction.
