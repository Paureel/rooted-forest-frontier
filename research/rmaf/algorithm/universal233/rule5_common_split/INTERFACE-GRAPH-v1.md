# Exact graph interface and caller boundary

The exported result is `common_split_derived_minimum` in DerivedMinimum.lean.
Its ten trees, two literal label lists, representatives, markers and four Nat
costs are explicit. The two `OriginalSplit` inputs contain only an actual
nonroot original subtree lookup and a descendant-label permutation with one
side of the checked partition. No graph conclusion is stored in that type.

`IsMinimum` is a mathematical AF witness plus a universal lower bound. It is
not an executable oracle and carries no source-work claim. The output is the
same mathematical `IsMinimum` for the original trees. Its witness is derived
from actual local forests, with separate inner-label and outer-block
permutations retained in the proof. The release does not yet bind this witness
to the output of a concrete list-producing reconstruction program.

Both fresh markers are ordinary explicit local labels. No implicit root taxon
is introduced. Representatives may be any members of the opposite blocks.
Both partitions and both rooted original cuts are required. The proper-label,
restriction, freshness and local-minimum inputs are not inferred from a source
case name. Source Rule5.3.1 must construct all of them at its actual call.

For that caller the intended next steps are: derive the outside minimum one
from actual admitted source geometry; compute the marked outside minimum by
an actual polynomial bounded pretest; call the ordinary and marked inside
pairs at the actual guarded budget q-1; construct and check a literal original
forest; prove minimum/None semantics, proper current states and strict
recursive progress; and pay both calls and all local source operations.
These are consuming obligations, not assumptions accepted as an algorithm.

The original target's broad phrase "polynomial depth<=2 computations" does not
license a free exact oracle. A possible implementation is an actual depth01
test plus a proved cost-two witness; it remains a future caller construction.
