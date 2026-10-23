# Live restriction and recovery

The main Lean proof constructs actual child families from a parent family
whose open support has no occupied leafless child. It selects exactly the
live parent indices and preserves their child supports. It proves all four
cost equations and recovers the parent by close-both, extend-left,
extend-right or merge, with an explicit bijection preserving supports and
root ownership. Kernel checking is complete; fresh semantic and interface
review is pending.

`RestrictionDefs.lean` states the required `OpenBranchLive` premise only for
the parent boundary index. `RestrictionGeometry.lean` derives liveness for
every occupied child restriction. A nonboundary region cannot enter both
children: convexity would put it at the parent root. Every parent index has
a leaf, so each belongs to at least one live child index set. Repeated leaf
values do not identify indices or addresses.

`FamilyRestriction.lean` constructs the child `Family` on the subtype of live
parent indices. Its enumeration is selected from the actual complete,
duplicate-free parent enumeration. The support function is exactly
`A.support i.val (side :: a)`. The boundary is the index containing the child
root, if one exists. The proof establishes boundedness, convexity, liveness,
disjointness, coverage and root ownership. A region closed in the parent may
be this child boundary. Unused internal vertices remain unused.

`RestrictionCounts.lean` proves that the two child counts sum to the parent
count plus one exactly when the parent open index is live in both children.
Its proof counts the two filters on the original index list and proves that
their intersection has either zero or one element. The exact parent costs
are `cL+cR+bL+bR`, `cL+cR+bR`, `cL+cR+bL`, and `cL+cR` for the four cases,
where `bL` and `bR` are the actual restricted child boundary charges. These
equations account for closing a parent-closed region that owns a child root.

`SupportRecovery.lean`, `RecoverSplits.lean`, and `RecoverMerge.lean` give the
explicit maps from each constructed transition's indices back to parent
indices. They prove injectivity, surjectivity, exact support equality and
the boundary equation. Generic `Represents` lemmas then prove label
membership, block-count and cost equality. `FourTransitions.lean` packages
the four exhaustive cases in `FourRecovery`, with `ExactRecovery` including
the representation, count and cost equations. `ForwardNormal.lean` proves
that every forward constructor satisfies the required parent premise, and
`represents_normal` transports that premise across an exact representation.
These are the two directions of the family-level correspondence.

The independent normalization route proves the premise for the concrete
`toClosedAssembly` and `toOpenAssembly` functions applied to `normalize F`,
and exports their exact supports. It also constructs a valid raw family
with a leafless open incursion, proves that the raw premise fails, and proves
that normalization removes the incursion and satisfies the premise.
`NormalizedCorrespondence.lean` consumes these concrete functions and proves
their four-case recovery and exact child-support equations. The earlier
`normalized_assembly_exists` theorem is never treated as exporting supports.
This composition shares the normalization route's proof and is recorded as
integration, not as an independent derivation.

The main geometry, constructor, count and four reconstruction proofs were
written before reading the normalization proof. The separate charge route
uses local Boolean charges summed over parent indices, with explicit
conditional Family consumers. It constructs no geometric restriction and
supplies no adapter to `LiveIndex`. Both supporting routes remain subject
to fresh review. The main proof imports the normalization route only in the
final composition module; it imports none of the charge route.

The frozen X0 controls passed before proof construction: eight positive
families, four malformed inputs, five wrong-number/clean pairs, three
support-corruption/clean pairs and one valid-family/outside-premise incursion.
A numeric-blind checker copy missed all five wrong numbers and the outer
test rejected it. The tiny search checked 3,629 candidates across all binary
shapes with two through four leaves, including 317 valid families and 289
satisfying the premise. It found no counterexample. These are bounded exact
observations; the universal claims depend on the Lean proofs.

`RestrictionFixtures.lean` proves eight numeric bundles on the actual
constructed restrictions: parent count/cost, both child counts/costs and
both boundary charges. `RestrictionTolls.lean` states the five correct twins
of the frozen wrong-number claims. Five separate false files rewrite with
those twins and fail on the exact false arithmetic propositions. Full
fixture support/index comparison is performed by the independent graph
checkers. The fresh reviewer has independently completed 23 finite control
groups, including two extra corruptions that retain geometric validity and
all numbers while changing exact indexed supports; proof review remains
pending.

Actual main axiom-query counts are recorded per module: RestrictionDefs 3,
RestrictionGeometry 6, FamilyRestriction 7, RestrictionCounts 10,
ForwardNormal 4, SupportRecovery 11, RecoverSplits 3, RecoverMerge 5,
FourTransitions 3, NormalizedCorrespondence 4, RestrictionFixtures 8 and
RestrictionTolls 5. These queries include definitions and finite control
theorems. Supporting-route and dependency queries are separate; repeated
builds add no inventory entries. Accepted builds use Lean 4.35.0 and only
standard axioms. Failed elaborations, source snapshots and diagnostic logs
remain available and are excluded from accepted evidence.

Full G2 still needs color/mask admissibility, the executable tree/graph
interfaces and the instantiated dynamic program's correctness. Table and
backpointer refinement, exact runtime/reconstruction costs, unrestricted
algorithms and any exponential-bound improvement are outside this result.
The full BootLoops numerical validation suite was not run for this proof
increment. The local proof/control scripts use the workspace runtimes.
