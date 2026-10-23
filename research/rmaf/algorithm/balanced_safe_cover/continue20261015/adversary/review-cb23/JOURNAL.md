# Fresh nonauthor review of CB2/CB3

Started 2026-10-15 after completing the independent CB1 adversary artifact.
The CB1 infinite-family proof is excluded from this review.

## Scope and frozen review plan
Read completed SPEC-CB2, SPEC-CB3, RESULT and the pinned CB3 obstruction receipt.
Before parent implementation contact, freeze an independent transition comparator,
run positive and negative controls, then rebuild all 26 literal root-row
compilations on the ordinary six-leaf quotient-star source pair. Check dynamic
maximal-column/singleton closure, child prefix cost, implication, and exact mass.

## Lineage
Reuse only the already-frozen adversary/independent_cb1.py tree/conflict
instrument, SHA256 3e5ef9bb655ee5adb055c016fe19a311331ea99d8637af85f1ac65d7f04dfc83.
It shares no code with parent CB2/CB3. New transition code will be authored
from the completed specs before reading the parent implementation.

## Controls
Pending freeze and execution before root reconstruction or implementation read.

## Reconstruction and semantic trace
Pending exact six-leaf source H, all 26 root rows, closures and masses.

## RESULT scientific-text audit
Pending separate correctness/novelty objections, prominence and prose passes.

## Verdict
Pending. No universal complexity, novelty or Lean closure will be inferred from
finite tests, and C1/source/formal interfaces remain separately scoped.

## Control gate, before source scoring or implementation read

Design SHA256 8f6a2d04e92fe09f979fdaf0254881359aa66ec95aaa259beab5e85ef8a5996d.
Control fixture SHA256 bbcc3a643ed5aa9cc92ba45726494aee6390e84aacb600f57c716545f2d64cf7.
The initial script invocation found a syntax error (one extra closing
parenthesis in output assembly) before executing any code. That syntax was
repaired before the successful control gate; no control or scientific
expectation changed. Parent implementation still unread.

Executed: `./bootloops-python research/rmaf/algorithm/balanced_safe_cover/continue20261015/adversary/review-cb23/compare_cb23.py`.
Verbatim output:
`{"status": "CONTROLS_PASS", "corruptions_caught": ["delta_minus_one", "mass_numerator_plus_one", "duplicate_cut", "reverse_implication", "omit_raw_branch", "false_base_comparison"], "seconds": 0.0010067499999877327, "instrument_sha256": "037edd8594a9247296e2096e5268ad98df61a7057fdb6b8864e243e763f447b9"}`
The successful comparator hash is now frozen. The source leg is invoked by
importing its unchanged source_review function, preserving this first control
receipt without replacing its measured timing. Comparator values are exact
integers and Fractions; no tolerance or scientific threshold was tuned.

## Strict replay failure and semantic diagnosis

The first source reconstruction recovered the 26-row root and independently
computed optimum 3, then failed its strict all-profile comparison at row 29.
The unchanged comparator expected the stronger non-singleton fixed point:
branch edge 2 yields [96,160,192], while the receipt gives[96,416,672,960].
Before implementation contact, a diagnostic compiled all 26 rows with the
frozen comparator; their retained child prefixes and masses matched the
headline obstruction. No scientific claim was closed on the failed strict
comparison.

Parent implementation contact then read conflict_dag_solver.py lines11-58,
conflict_row_selector.py lines10-66 and the necessary conflict_solver.py
primitives/call sites. forced_closure stops at the first nonsingleton minimum
row after one projection (dag lines14-18). SPEC-CB2's explicit stopping
sentence supports that reading, but its first repeated-projection phrase
can suggest the stronger fixed point. This is recorded as a clarification,
not a solver-correctness failure. The post-contact mode wrapper is declared
as such and does not replace the frozen comparator.

Executed reconstruct_modes.py; verbatim summary:
`{"status": "PRIMARY_OBSTRUCTION_CONFIRMED_WITH_CLOSURE_INTERPRETATION_NOTE", "all_rows": 26, "original_optimum_by_partitions": 3, "strict_profile_mismatch_count": 16, "minimum_unit_children": 3, "best_row": 960, "best_mass": [9, 7], "semantic_implication_pairs_checked": 162, "parent_profiles_exactly_replayed": true, "seconds": 0.07414716699986457}`

The16 profile mismatches all arise from the same edge 2 child residual. Both
interpretations retain identical branch-prefix masks, costs, representatives
and masses for every row. All 162 ordered child-state implication pairs
across the two modes agree with exhaustive Boolean semantics on ten edges.
Every child delta equals its number of distinct original cuts. All1024
original source cutsets agree with the independently computed C1 finite test.
The exact best profile is3 unit cuts at row 960, giving 9/7 at 7/3. Every row
has at least 3 unit cuts, so every base c<3 has mass>=3/c>1 on this root.

Executed check_source_causes.py: all 26 original rows and all 26 literal causes
match; all pinned source hashes match. The empty wrapper text control rejects
solve(None,None,-1) and accepts solve(None,None,0). It found a RESULT line 63
formula error requiring max(0,n-1) or an explicit nonempty precondition.
Source-cause/control body runtime was0.0025053330000446294 seconds.

## Text review and final scope

REVIEW.md gives the exact result and four narrow text/spec recommendations.
Fresh referee-sim and prose-lint reports are beside it. Correctness and novelty
objections are separate. C1/source-bound formalization, universal optimality,
old compiler/axiom audits and stronger reduction history remain separately
scoped; prior release reviews were not duplicated. The CB1 infinite-family
proof is explicitly unreviewed by its author. No Lean file or closure claim
was produced. No broad census or long run was launched. Parent files and
original receipts remain unchanged by this review.
