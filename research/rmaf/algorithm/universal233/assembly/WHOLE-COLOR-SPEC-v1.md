# Public exact whole-source color specification

This file is the shared statement for independent assembly proof viewpoints.
Candidate coverage/clearing proofs in assembly/*.lean are not shared while
unfinished. Complete frozen source_coverage/, cut_realization/, core/,
geometry/ and integration/ are development inputs.

For three nonempty, pairwise label-disjoint parent blocks A,B,C partitioning
leaves S, define exactly

    taggedColor A B ca cb cc x :=
      if x in A then 3*ca(x)
      else if x in B then 3*cb(x)+1
      else 3*cc(x)+2.

Untouched local color is constant0. A single cleared target vertex v uses
ca(x)=VertexGeometry.colorLabel T v x on that parent. A joint middle clearing
at distinct target vertices v,w uses

    jointLabel T v w x := 4*colorLabel T v x + colorLabel T w x.

All original address regions are<=3, so this encoding is injective on the
relevant pairs. For a proper internal target vertex with no leaf at it,
selected labels have region<3; exact nonempty region counts come from the
frozen actual original-label geometry, including original target root having
only two occupied directions.

Required source hypothesis: all source leaves are target labels; original
labels distinct. Exact source parent partition validity yields coverage and
parent disjointness; these may be printed as explicit input hypotheses if
not yet derived, but the conclusion must not assume its color cardinality.

Mass task: derive distinct ORIGINAL INPUT colorcount for literal taggedColor,
then apply actual generate_rawQ_mass, counting every output-list occurrence.
For each clique survivor, two parents are colored by v and the third is
constant; occupied original target spans give>=2 colors in each cleared
parent, so total>=5. For the four chain ownership alternatives, clearB(v)
andC(w), clearB(v,w) jointly, clearA(v) andC(w), clearA(v) andB(w).
When jointColors B T v w has>=3 members, all four total counts are>=5.
For exactly2 joint colors, use the paid diagonal B-joint versus A-andC:
total counts>=4 and>=5, respectively. No same-parent independent cut union.

Required consuming bounds for rational c>=2: clique sum<=3*c^-4; four-chain
sum<=4*c^-4; diagonal sum<=c^-3+c^-4. These are whole-source mass losses, so
initial hard2 is already paid; do not multiply by another c^-2. Endpoint
branches add2/c only at the full hard-call recurrence. At2.33 these full
three bounds are strictly<1, as previously checked conditional arithmetic;
new task is actual-source color/generator interface, not arithmetic alone.

The whole source generates actual original cuts and finite-budget refinement.
Original hard-branch P/refinement safety, target clearing at all emitted
blocks, whole-state history, polynomial prefix implementation work and the
remaining pair-case proof are separate consuming obligations. No complete
algorithm claim follows from this mass assembly alone.
