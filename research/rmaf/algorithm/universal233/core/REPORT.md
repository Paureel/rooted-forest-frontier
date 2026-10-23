# Colored-source core: local graph proofs and executable candidate

The universal source core remains OPEN. This arm proves local cherry statements
on actual rooted graphs and supplies a total executable candidate, but it does
not prove recursive coverage or original-cut realization. All three complete
algorithm milestones therefore remain OPEN.

## Proved graph statements

`CoreGraph.lean` uses the unchanged `RMAF.Tree` type. Executable `subtree` lookup
determines actual vertices and leaf occurrences. Adjacency consists of actual
parent–child edges, and connectedness means a finite graph walk. Source
partitions have exact terminal membership and disjoint connected supports.
They have no assumed coverage, contraction, source-cut realization or mass
field.

The Lean kernel checks these universal statements:

- `mixed_cherry_singleton`: in every monochromatic source partition, a cherry
  with different child colors has a child that is the only current leaf in its
  block. A nontrivial walk from either child to another terminal visits the
  actual parent; both blocks cannot extend because their supports are disjoint.
- `unique_color_singleton`: a color used at exactly one current leaf forces
  that leaf to be the only current leaf in its block.
- `homogeneous_cherry_coarsening`, in `CherryCoarsening.lean`: every
  monochromatic source partition admits a valid monochromatic coarsening that
  joins the two same-color cherry leaves. Refinement is explicitly the
  implication from equality of the old block owners to equality of the new
  owners.

The homogeneous construction covers a parent that is free, belongs to either
cherry block, or belongs to a third block. It merges the cherry supports and
adds their actual parent. For every other support it removes that parent. The
proved walk lemma `Walk.avoid_one_neighbor` preserves connectivity because such
a support cannot contain either cherry leaf and hence has at most one neighbor
of the parent. The argument also permits the parent to be the original root.
It retains degree-two vertices throughout the graph proof.

These results establish local graph statements. Applying them repeatedly to
`normalize` and `erase` still requires the contraction, suppression and
original-label maps stated in `FIRST-GAP.md`.

## Executable candidate

`CoreProgram.lean` implements the proposed rule order without an optimum
query: normalize homogeneous cherries; finish at one color; detach a unique
color; otherwise branch on both leaves of a mixed cherry. Leaf groups retain
all original labels and their original source addresses. Group deletion
suppresses unary nodes and the current root while retaining the survivor's
original address. The candidate reports root cuts, repeated cut addresses,
invalid mixed-cherry selection and invalid deletion as explicit refusals.
Those refusal cases have not all been proved unreachable on valid inputs.

The budget is a structural recursion argument. A child that would exceed the
budget is counted as a pruned prefix. The kernel proves, for every budget `q`
and every program state,

```
visited + 1 <= 2^(q+1)
childAttempts <= 2 * visited
visited + childAttempts + 3 <= 3 * 2^(q+1).
```

The count includes failed, root, duplicate and over-budget child attempts.
These inequalities bound recursive construction work. A full O*(2^q)
statement also needs polynomial per-node size and operation counts, including
output construction and reconstruction. That proof remains OPEN. No
polynomial-time claim is made for exponential generation.

`CoreInvariants.lean` proves that normalization preserves the ordered
original-label payload and group purity. It also proves that every emitted
cut record has distinct nonroot addresses and that its recorded number of
blocks equals its recorded number of cuts plus one. Actual source-edge
validity, absence of leafless residual components and nonredundancy remain
separate graph obligations.

## Executed checks

The complete sources build with the project-pinned Lean 4.35.0 compiler through
both `./bootloops-lean` and `./bootloops-lake`. The source-bound replay at
`replay/20261015T063857Z/` copied and compared every current module and the
unchanged `RMAF.lean` dependency, retained SHA-256 hashes, compiled each copy
from source, and checked all 112 explicit declarations. Only the standard Lean
axioms `propext`, `Quot.sound` and `Classical.choice` occur in their transitive
axiom audits. The accepted sources contain no unresolved Lean proof or custom
unproved axiom, and use no `native_decide`.

Nine literal controls pass by kernel reduction. They include both crossed
quartet cores with charge two, insufficient budget, homogeneous coarsening,
three colors, the original root, a singleton source and duplicate-label
refusal. The control sheet was written before the program was executed.
Partition display order is normalized only for literal control equality.

Three deliberately false propositions were rejected specifically because
`decide` proved them false: one retained mixed-cherry branch still yielding
both crossed-quartet cores, an original-root cut on a singleton source, and
preserving every homogeneous-cherry input partition exactly rather than by
refinement. Their source files and compiler errors remain in the replay.

The replay verdict is:

```
PASS: source-bound compilation, 112 complete axiom audits, 9 positive controls, 3 rejected false controls
PASS: 112 / 112 declarations; only standard Lean axioms ['Classical.choice', 'Quot.sound', 'propext']
```

Compilation and these controls were run by the author. They provide no fresh
nonauthor reconstruction. The complete earlier X0 census was not repeated and
its large raw receipt was not read.

## Remaining consumer obligations

`FIRST-GAP.md` states the exact unresolved interfaces at their calls. Before
this proof model can consume an existing ordinary solver partition, the
Boolean partition/minimal-embedding checks must be converted to its connected
supports. Within the candidate, the first unresolved graph simulation is
`CoreProgram.step`'s `normalize` call at line 110. The contraction map must
carry a suitable coarsening to the grouped source graph and preserve its
original-label refinement lift. The later `erase` call and original source-cut
recording require their own simulation invariants.

The universal mass bound, realized-cost lower bound, full recursive coverage,
original cut realization, all valid-input refusal exclusions and full
polynomial per-node construction cost remain OPEN. No connected-overlap
geometry, full rMAF scaffold, completed-component/reverse-contraction theorem,
2.33 algorithm runtime or novelty claim follows from this arm.

## Provenance and replay

The target files and the retained X0 report were read directly. The X0
`prototype.py` was read as DEVELOPMENT contact before writing the executable
candidate. The candidate and controls therefore make no independence claim
against that prototype or its pinned fixtures. Only graph/type vocabulary was
read from the older Lean source modules; no pending sibling or safe-cover
result was imported. `RMAF.lean` is imported for its existing tree vocabulary;
the candidate calls none of its exhaustive assignment or optimum functions.

Run `core/replay.sh` from any directory for a new source-bound compiler receipt.
It rejects unexpected compiler failures, missing audits, any unaccepted axiom,
and any accepted false control. `make_audit.py` regenerates the complete explicit
declaration audit after a deliberate source change; `check_audit.py` checks its
full expected declaration set. The original frozen protocols, X0 results,
upstream verification scripts and integrity pins were preserved.
