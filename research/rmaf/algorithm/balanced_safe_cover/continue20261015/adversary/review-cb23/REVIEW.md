# Fresh CB2/CB3 review

Verdict: the six-leaf all-row obstruction is CONFIRMED as finite source-derived
evidence against the specified uniform one-row recurrence. Every one of the
26 minimal root rows retains at least three unit-cost children, and the best
exact mass at 7/3 is 9/7 at row 960. No solver-correctness failure, general runtime
lower bound, safe-cover impossibility, novelty result, or Lean closure is
claimed. C1's universal source-model correspondence and formal interfaces
remain open. The CB1 infinite-family proof was outside this review.

## Independent reconstruction

The design and controls were frozen before parent implementation contact.
`compare_cb23.py` reuses the previously frozen, independently authored
`adversary/independent_cb1.py` tree/conflict instrument, SHA256
3e5ef9bb655ee5adb055c016fe19a311331ea99d8637af85f1ac65d7f04dfc83.
The new transition comparator's control-passing SHA256 is
037edd8594a9247296e2096e5268ad98df61a7057fdb6b8864e243e763f447b9.
The completed specs and claimed receipt values were read before the review;
they were inputs under test, not independent expected data. No parent
implementation code was read until the new controls had passed and strict
source reconstruction exposed a residual-row mismatch.

The independent tree representation keeps literal child order, whereas the
receipt canonicalizes it. Original source edges were therefore matched by
their distinct descendant-label sets, without importing the parent's parser.
The reconstructed trees yield exactly the receipt's 26 original conflicts and
all 26 literal causes, including the source-span mask960 for {a,b,c}.
Enumerating ordinary label partitions independently gives optimum 3. Every
one of the 1024 original source cutsets agrees with the finite C1 equivalence.
The source and target have no common nontrivial pendant clade. A stronger
reduction history was not audited.

The new controls cover empty and singleton closure, four CNF direction
assertions, every triangle/four-of-five row closing to one cost 2 terminal
child, and a cost/implication dominance twin. All six corruptions were
rejected: changed delta, changed mass, duplicate cut, reversed implication,
missing raw branch, and false base comparison. The control receipt was
written before the new source-row test. The source replay also rejects
corrupted stored delta, mass and residual row values.

## Closure interpretation and exact trace

The independently frozen design continued column projection and row
subsumption to a fixed point even after no singleton remained. The parent
implementation instead projects once, then stops immediately when the
minimum projected row is nonsingleton: `conflict_dag_solver.py:14-18`.
The explicit stopping sentence in SPEC-CB2 supports the implemented reading;
the opening phrase repeatedly apply can also suggest the stronger reading.
This is a specification clarification, not a correctness counterexample.

The difference is concrete. At root row 29, branch edge 2 has cost 1 and no
forced cut. The receipt/implementation residual is
[96,416,672,960]. A second quotient gives [96,160,192]. Sixteen of the 26
stored profiles differ in this same edge 2 child state under the stronger
fixed-point reading. No other raw child-state difference occurs.

Both interpretations retain exactly the same original prefix cut masks,
prefix costs, branch representatives and rational masses for all 26 rows.
The stronger independent comparator had been frozen before implementation
contact. The literal stop-mode wrapper was written after inspecting the
implementation, and that contact is explicitly marked in its receipt; its
exact state replay is not presented as blinded certification.

All26 implemented row compilations replay exactly, including forcing steps,
raw and retained states, cut masks and costs. Every prefix delta equals the
number of distinct original cuts. Across both interpretations, all 162
ordered child-state pairs across the two modes were checked against
all 1024 Boolean edge selections; the monotone-CNF implication predicate
agreed in every case. Every recorded prune has a retained child of no larger
prefix cost whose residual is implied by the pruned residual. The minimum
unit-child count is3. Row960 retains pendant c, pendant a and pendant b,
each at cost 1, giving 3*(3/7)=9/7.

For any base c<3, those three unit children alone contribute3/c>1 for every
row. This blocks the stated uniform one-row cut-budget recurrence. It says
nothing by itself about how many compiled states are globally reachable,
cache amortization, multirow macros, another residual representation, or
partial guarded certificates. The production code does not require the
mass test to pass before searching; `choose_row` returns the least mass and
the solver proceeds. The failed condition is a proof obligation.

## Findings in RESULT.md

1. **[P2] Empty-input optimization wrapper, line 63.** The printed wrapper
   `solve(S,T,n-1)` passes -1 for the valid empty input and raises ValueError.
   The clean twin `solve(None,None,0)` returns cost0. State
   `solve(S,T,max(0,n-1))`, or give the wrapper an explicit nonempty
   precondition and handle the empty input separately. The existing solver's
   handling of a valid zero budget is correct; this is a document formula.
2. **[P3] Name the blocked proof obligation, lines117-120.** The phrase
   choose_row's required mass<=1 call can be read as an executable check.
   `conflict_row_selector.py:32-36` does not test mass<=1, and search continues
   at lines54-61. Suggested wording: the uniform recurrence proof requires
   mass<=1 at choose_row; the returned minimum mass9/7 violates that
   obligation. The surrounding limitation to a recurrence certificate is
   already correct and prominent.
3. **[P3] Clarify closure stopping in SPEC-CB2 and result scope.** State that
   projection repeats after forced singleton cuts and stops at the first
   nonsingleton projected minimum row. If a full non-singleton fixed point
   is intended instead, version that change and preserve the old receipt.
   The retained obstruction survives both interpretations on this fixture.
4. **[P3] Numeric spacing.** Numerous prose tokens omit a space or equality
   sign before a value, for example below2.3391, at0, has26, base7/3,
   tau0 and theta1/2. These obscure the prose and should be normalized while
   retaining exact fractions and literal code masks.

No parent source or result file was edited; this review owns only its new
subdirectory and new review receipt prefix. RESULT's opening lines3-7 and
its C1 caveat at34-37 correctly keep all main milestones open. The all-row
obstruction's exclusions are stated beside the numerical result at117-121,
and its finite-source/formal distinction appears at136-142. The existing
Lean compiler/axiom and old release-control claims were not re-audited, as
requested; this review adds no kernel-verification claim.

## Receipts and reproducibility

All files below are in `research/rmaf/results/`:

- algorithm-balanced-cover-continue-review-cb23-controls-v1.json: frozen
  controls, six corruption catches,0.0010067499999877327 seconds.
- algorithm-balanced-cover-continue-review-cb23-source-modes-v1.json: both
  complete26-row reconstructions, implementation replay, source partitions,
  all-source-cutset checks, implication checks and mismatch details;
  0.07414716699986457 seconds.
- algorithm-balanced-cover-continue-review-cb23-source-causes-v1.json: all 26
  literal causes, pinned source hash checks and the empty-wrapper clean/bad
  twins;0.0025053330000446294 seconds.

The first strict source comparison failed on row 29 before writing a false
confirmation receipt. The unchanged comparator, its failed assertion, the
closure diagnosis, and the declared post-contact wrapper are retained. The
small measured source legs stayed below a tenth of a second; no broad census
or long run was launched. Scripts remain explicitly one-shot problem-review
instruments rather than additions to the general toolkit.
