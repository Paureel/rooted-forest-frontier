# Fresh restriction review

Phase 1: independent finite evaluator, controls and receipts.

## Independence record
- TARGET.md was the first project source read.
- This skeleton was created immediately after reading TARGET.md.
- No author/route/adversary proof or checker body has been read.
- Evaluation design will use the target, control declarations and shared semantics only.
- Checker and source hashes will be frozen before evaluation.

## Work status
- Independent semantics inspection: complete for the finite evaluator.
- Independent checker construction and source pin: complete before execution.
- Frozen control battery and hostile controls: 23/23 groups pass; copied numeric-blind instrument rejected.
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

## First execution: measured pilot

The original target/control hashes match PRECONSTRUCTION-SHA256.json. Eleven
source/design/input files were frozen at 2026-10-14T14:55:09.293947+00:00 in
PHASE1-SOURCE-PIN.json. Original checker SHA256:
`ee4e7627b249ffb2948e0c5f3ac5edcffca0e0a98233df2c5a8d69268b47aba1`.

Command:
`./bootloops-python research/rmaf/triple_dp/family/transitions/restriction/fresh_review/run_controls.py --pilot --output research/rmaf/results/triple-family-transitions-restriction-fresh-phase1-pilot-20261014T145509Z`

Verbatim output:
```
{"elapsed_seconds": 0.00020841700097662397, "passed": true, "rows": 2, "stage": "pilot"}
```

The two pilot rows are R1 positive and the clean/wrong toll pair, run through the
same evaluator and comparator as the full battery. Full scope has 23 row groups
per instrument and two instruments. At the pilot's mean rate, the crude linear
projection is 0.0048 seconds for 46 groups, excluding interpreter startup and
allowing larger graph cases to cost more. This is a planning estimate, not a
promised duration. Progress remains retained row receipts. Full source checks
run both before and after every evaluation. No new proof body has been read.

## Phase 1 executed outcome

**Finite control battery: PASS. Universal proof: NOT REVIEWED.**
No evaluator or control edits occurred after the initial source freeze. All
11 source hashes matched before and after the pilot and both full instruments.
No new restriction, alternate-route, adversary, or previous checker bodies have
been opened. The completed merge review was neither executed nor edited.

Command:
`./bootloops-python research/rmaf/triple_dp/family/transitions/restriction/fresh_review/run_controls.py --output research/rmaf/results/triple-family-transitions-restriction-fresh-phase1-full-20261014T145509Z`

Verbatim output:
```
{"numeric_blind_elapsed_seconds": 0.0012861670002166647, "numeric_blind_escapes": ["omit-close-toll", "parent-closed-root-is-not-child-boundary", "unused-root-invented", "double-count-merge", "charge-extended-open"], "numeric_blind_outer_gate_accepts": false, "original_denominator": 23, "original_denominators": {"corruption": 3, "hostile": 2, "malformed": 4, "outside_premise": 1, "positive": 8, "wrong_number": 5}, "original_elapsed_seconds": 0.001450040999770863, "original_outer_gate_accepts": true, "original_passes": 23, "passed": true, "plant_checks": {"all_five_wrong_numbers_escape": true, "mutant_denominators_complete": true, "other_mutant_rows_pass": true, "outer_gate_rejects_numeric_blind": true}, "stage": "full"}
```

Measured integer results, retrieved from `original.json`, rows with category
`positive`, using each row's `evaluation.summary` (count/cost pair in columns):

| ID | Recovered transition | Parent count/cost | Left count/cost | Right count/cost | Toll |
|---|---|---:|---:|---:|---:|
| R1 | closeBoth | 2 / 2 | 1 / 0 | 1 / 0 | 2 |
| R2 | extendLeft | 2 / 1 | 1 / 0 | 1 / 0 | 1 |
| R3 | extendRight | 2 / 1 | 1 / 0 | 1 / 0 | 1 |
| R4 | merge | 1 / 0 | 1 / 0 | 1 / 0 | 0 |
| R5 | closeBoth | 2 / 2 | 1 / 0 | 1 / 0 | 2 |
| R6 | closeBoth | 3 / 3 | 2 / 2 | 1 / 0 | 1 |
| R7 | extendLeft | 3 / 2 | 1 / 0 | 2 / 2 | 0 |
| R8 | merge | 3 / 2 | 2 / 1 | 2 / 1 | 0 |

Each positive row retains actual children, live parent index lists, child field
validation reports, exact count and cost equations, and tagged-index bijection
rows carrying both reassembled and parent support sets. These are computed
objects, not assertions copied from the expected fields.

Malformed inputs are rejected with the following retained reasons:
- duplicate-index: `finite.nodup: duplicated index`
- omitted-index: `finite.complete: enumeration differs from support domain`
- overlap: `disjoint: vertex has two indices`
- wrong-root-owner: `root_spec: root owner differs from boundary`

All five wrong-number and all three supplied corruption pairs accept the clean
claim and reject the corrupted one. Each receipt records the mismatching field,
actual value and claimed value. The numeric-blind copy preserves every other
check but accepts both twins of all five wrong-number pairs; the outer gate
rejects the instrument, with complete denominators and the other 18 groups
passing. The original checker remains byte-identical to its pre-execution pin.

The raw incursion is a valid parent. Its left live indices are `[a,b]`, its right
live index is `[o]`, and `OpenBranchLive` is false. The left live restriction has
boundary none; the right restriction has boundary o. The main target evaluator
refuses transition recovery outside its premise. This is neither a malformed
family nor a counterexample to the pinned target.

Independent hostile controls:
- H1: four x-labelled leaf vertices and four distinct indices, with finite list
  `[X,right-b,x,right-a]`. The constructed left list is `[X,x]`, retaining parent
  enumeration and distinct identities. Swapping the singleton supports of X and
  x leaves a valid child and unchanged numbers but fails `left_regions` equality.
- H2: adding the unused nonroot child vertex 0 to a's support at 00 preserves
  convexity, leaf ownership, child boundary none and all seven numeric fields.
  The clean claim passes; the changed support fails `left_regions` equality.
  Both corrupt child families are explicitly validated in their receipts.

## Independence and acceptance ruling

This is a fresh nonauthor evaluator in Python standard library, reconstructed
from the target and shared Family definitions. Its graph/BFS core, restriction
constructor, tagged transition constructor and comparator have no code imports
from any project evaluator or Lean proof. Shared layers are the pinned target,
its public expected controls, the address-tree representation and the Family
semantics. This cannot independently certify a mistranscribed target or shared
semantic definition; it checks the printed statement's finite consequences.

The supplied expected fixtures were visible before implementation, as required
for reproduction. They were not generated by this evaluator; no fitting,
tolerance selection, or post-output adjustment was performed. The two added
controls and both comparator versions were pinned before any execution. The
pilot was used solely to measure runtime; it caused no source change. No
held-out-digits or floating-point precision claim is made: supports, identities
and arithmetic are finite and exact. Acceptance-gate precision doubling and
leave-one-out fitting checks are inapplicable to this integer/set evaluator.

The raw run receipts are immutable review evidence. PHASE1-SOURCE-PIN.json is
the replay input pin; the driver checks every hash both before and after running.
Any later source change requires a new version and new explicit review. No
larger census, universal theorem check, normalized-assembly premise transport,
Lean rebuild, axiom audit or consuming-interface review has yet been performed.
Those are phase 2, pending the parent's final proof pin. This report must not be
promoted to VERIFIED-CLOSED for the universal target on the strength of these
finite cases.

Receipt metadata caveat: the per-instrument `started_utc` field is assigned when
the completed receipt is assembled, so it is a completion timestamp despite its
name. The separately recorded monotonic `elapsed_seconds` is measured from the
start of the trial. This does not affect case values, source hashes or gates;
the frozen receipts and source are preserved, with the naming error disclosed.
