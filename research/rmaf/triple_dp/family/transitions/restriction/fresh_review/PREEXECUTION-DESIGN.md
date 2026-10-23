# Fresh restriction review

Phase 1: independent finite evaluator, controls and receipts.

## Independence record
- TARGET.md was the first project source read.
- This skeleton was created immediately after reading TARGET.md.
- No author/route/adversary proof or checker body has been read.
- Evaluation design will use the target, control declarations and shared semantics only.
- Checker and source hashes will be frozen before evaluation.

## Work status
- Independent semantics inspection: pending.
- Independent checker construction and source pin: pending.
- Frozen control battery and hostile controls: pending.
- Phase 2 proof/axiom/interface inspection: deferred until parent supplies final proof pin.

## Required receipts
All eight positive cases; four malformed families; five wrong-number clean pairs;
three corruption clean pairs; valid raw incursion outside the premise; numeric-blind
COPY caught by the outer gate; independent equal-label/index hostile control;
independent geometrically valid support corruption.

## Phase 1 design fixed before code/evaluation

Read: TARGET.md in full; controls.json in full; PRECONSTRUCTION-SHA256.json
(the initially requested extensionless name does not exist). The target pin
contains exactly TARGET.md and controls.json.

Read shared semantics: FamilyAssembly.lean lines 11–26, 58–79; ConnectedRegions.lean
lines 7–14; TripleDP.lean lines 199–209. The broad FamilyAssembly excerpt also
exposed the old generic FiniteIndex/indexSum utility proofs (lines 28–56), and
neighboring historical theorem fragments were visible. No restriction, route,
adversary, or previous fresh checker/proof body was opened. The common semantic
substrate is expressly shared; no claim of independence from those definitions
is made. The independent algorithm will use graph connectivity/unique BFS paths,
not those Lean proof steps. File-path discovery exposed filenames only, not
contents of other review or proof sources.

Tool choice: the toolkit index and trust/GUIDE.md were consulted. Trust verifies
IBP reductions and cannot evaluate finite labelled tree families. This one-shot
finite evaluator is required independently by prove-protocol and deliberately
reuses no project checker implementation; no toolkit modification is warranted.

Derived design (not a retrieved result): parse the rooted binary tree into a graph;
check finite enumeration, bounds, path containment, leaf witness/coverage,
disjointness and root ownership. Select live indices using leaf vertices, restrict
exact support, infer each child's root owner, classify the parent from its
boundary's two live flags. Reassemble tagged disjoint child indices, identifying
only the two distinguished boundaries in merge. Map each reconstructed index to
its original parent identity and check bijection, exact supports, and boundary.
Measure counts, costs and closing tolls from constructed families. Independently
check count overlap and cost equations; never substitute expected fixture values
into computation.

Predeclared failure rules: every positive expected field must match exactly;
all malformed inputs must fail family validation; every corruption/wrong number
must fail alongside a passing clean twin; the raw incursion must validate as a
parent but fail the premise; its leafless child occurrence must be omitted from
live indices. The numeric-blind copied comparator must let all five wrong-number
claims escape, and the unchanged outer gate must reject that instrument. Missing
or extra controls fail the denominator gate. Any unexpected outcome halts review.

Timing: unknown—measuring on the R1 positive/wrong-toll pilot first. The full
scope is the frozen battery plus exactly two independently authored hostile
controls, with no census or size growth. Progress unit is a case receipt.

Hostile controls fixed before evaluator execution:
H1 uses four leaves all labelled x and four distinct parent indices, including
both "x" and "X", in deliberately shuffled finite order; swapping the two
left singleton supports leaves a valid family and unchanged numbers but must
fail exact index/support correspondence.
H2 uses four closed singleton regions at parent addresses 000, 001, 01, 1.
Adding the unused left-child internal vertex 0 to its singleton region at 00
preserves child validity, boundary and every number, but must fail exact support
restriction. The child root stays unused.
