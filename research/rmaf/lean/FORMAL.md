# Formal checkpoint

Target pin: `../spec.json`. Ordinary rooted MAF without a rho leaf; components
are leaf-partition blocks with equal rooted restrictions and vertex-disjoint
minimal embeddings in both trees.

No indexed BootLoops package provides a rooted-MAF formalization or a Lean
proof checker. This problem-specific library uses Lean's kernel and standard
library, rather than repurposing numerical integration tools.

## Definitions and intended use

`Tree` is a finite rooted binary syntax with natural-number leaf labels.
`Instance` adds bijective common labelling by `0, ..., n-1` via list permutations.
`RootedIso` permits child swaps and preserves labels. `sameShape_correct`
proves that the separate executable Boolean test recognizes exactly this
inductive relation.

`restrict` retains selected leaves and suppresses unary vertices. The minimal
embedding checker retains intervening unary vertices for vertex-disjointness:
it uses full rooted paths once the selected leaves occupy both children, but
descends below an unneeded root when only one child contributes. Empty
selections have no restriction or embedding. No root-marker leaf is added.

Use this library to formalize candidate finite forests, regression controls,
and correctness of exhaustive assignment search. It is not a competitive FPT
solver. Enumeration produces `n^n` tag assignments before filtering duplicates.
Each assignment gives a partition by equal tags; empty tags are discarded.
The solver returns an optional minimum-cost assignment within this model.

Published definition locator: Mestel--Chaplick--Kelk--Meuwese,
arXiv:2409.18634 v2, Section 2, PDF pages 3--4 and footnote 2. I read that
definition directly, not the other routes' evaluators or journals.

## Checked lemmas and scope

The executed build and `#print axioms` audit check **21 theorems**:

- Rooted-isomorphism checker reflexivity and equivalence to `RootedIso`.
- A restriction containing every leaf returns the original tree.
- Assignment enumeration completeness and soundness for bounded lists.
- Generic minimum selector soundness, optimality, failure characterization,
  and existence from a feasible witness.
- Assignment solver optimality across *every* bounded assignment, and
  validity of the returned assignment's length and tags.
- Four-leaf positive/negative controls and a finite endpoint-only branch kill.

Every theorem's dependency list is retained in `audit/certificate.json`.
Only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) occur.
The finite computations use kernel `decide`, not `native_decide`. There are no
unfinished proofs or custom axioms. This is kernel verification; independent
semantic review is still required before declaring a research claim closed.

## Independent finite witness

Trees are `((0,1),(2,3))` and `((0,(1,2)),3)`. Their full restrictions differ,
but `{{0,1,3},{2}}` is an agreement forest of size two in the executable model.
Enumeration of all `4^4 = 256` assignments gives minimum two. Every feasible
assignment isolating cherry endpoint `0` or `1` has at least three components.
Thus an endpoint-only isolation branch misses all optimum assignments on
this pair. This witness was constructed without reading the other routes.

The plant `{{0,2},{1,3}}` on the first tree has compatible two-leaf
restrictions but overlapping embeddings. The checker rejects it; the
separate `negative/FalseControl.lean` attempts to prove it accepted and must
fail. This verifies that topology-only acceptance would be caught.

## Remaining semantic interface and next actions

The universal solver theorems are exact statements about the specified
executable assignment/embedding model. They do **not** finish formal
equivalence to the paper's graph-theoretic definition. Remaining obligations:

1. Prove graph correspondence for binary syntax, rooted restrictions, and
   minimal vertex embeddings (especially unary path interiors).
2. Prove that every nonempty-block set partition of the canonical taxon set
   is represented by a bounded assignment.
3. Prove singleton-forest feasibility for every well-formed `Instance`, so
   search success follows without supplying a witness.
4. Formalize each proposed reduction and branch and its exhaustive coverage.
5. Add a full cost model and prove the worst-case bound in component parameter
   `k`, including measure conversion and polynomial work per search node.
6. Obtain fresh semantic and independent verification of the composed result.

No improved exponential algorithm or complete rMAF algorithm theorem is
claimed. Small-instance checks do not imply universal branching correctness.

## Replay and change record

From the workspace root:

```sh
./bootloops-python research/rmaf/lean/audit.py
```

The script runs the tracked Lake build, replays all theorem axiom prints,
checks their exact presence, verifies that the false statement fails for the
expected reason, and writes build/axiom/negative logs plus a source hash.
An unexpected success of the false control makes the audit fail.

2026-10-14: Initial model and 21-theorem checkpoint. Final first clean build
took approximately nine seconds; the full axiom replay took approximately
seven seconds. These measured pilot times justify replay on this small
checkpoint, not unrestricted larger finite searches.
