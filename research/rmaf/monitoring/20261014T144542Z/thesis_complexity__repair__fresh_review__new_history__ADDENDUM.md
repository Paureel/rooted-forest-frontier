# New history evidence

Status: checked reachable application-premise failure. The first review and its receipts remain unchanged.

The new candidate JSON was read before creating this addendum. Its coordinator implementation is not read or imported. This addendum will use the existing independently written fresh-review evaluator, with explicit lineage and new frozen controls, to replay the unprotected twelve-leaf initial trees and branch sequence C,A,C,A. The target is the unqualified source-history implication to the outside-b premise. No runtime inequality or explicitly conditional local theorem is presently accepted or refuted by this evidence.

## Pre-execution checks

Completed by the source checks and 60 exact replay checks below.

## Replay

Completed; the reachable outside-b application premise fails, and the actual C continuation counts two invocations.

## Formal certificate

Completed after the independent replay: eleven source-certificate statements and two supplemental checks compile with standard logical axioms only.

## Ruling

The correction is confined to the first review's proposed unqualified application lemma. Its prior files remain unchanged; this addendum supersedes that lemma.

Source check: printed p120 expressly resets P=Q=empty when a G3 A2BC/A3BC invocation makes only one recursive call because of protected edges. Printed p118's G1 assignment puts P={a} in a C child of an A2BC invocation and Q empty; it does not require all three nominal calls to be legal. Thus a new empty-credit analysis block can begin with inherited physical protection. The depth rule on printed p110 uses physical protected edges, so resetting analysis credits does not make every equal-depth pair eligible. These facts will be checked at their exact use sites in the replay.

A copy of the first review's fresh evaluator, with only the relative root and output path changed, reran its 37 exposed control records in 0.013702625 s. Its new receipt is `results/thesis-runtime-repair-fresh-review-history-controls.json`. No original review receipt was overwritten.

## Independent replay result

The replay completed 60 exact checks in 0.008284875 s. Starting from both unprotected twelve-leaf trees under unary labelled rho, the source-legal full-call-tree branch sequence C,A,C,A reaches J at budget 16 with P={a},Q empty. J selects (x,y), uses A3BC with exactly three pendants X,W,Y, has all three legal branches, and has e active roots x,y,h. The protected sibling of a is b={W,X,Y,x,y}, so x belongs to b.

The machine-readable failure is the outside-b conclusion: membership-indicator LHS=1, required RHS=0, residual=1. This is a reachable application-premise counterexample. It contradicts the unqualified source-history lemma proposed in the first review's RULING.md; that file is preserved, and this addendum supersedes that proposed lemma. The explicit conditional geometry theorem assumes outside-b/original eligibility and is not contradicted.

The source mechanism is visible at the new I, before J: a and x have F1 depth 5, while their F2 depths are 4 and 7. Physical a protection remains from the preceding block even though the G3 sole-child rule reset P and Q to empty. Consequently (x,y) is ineligible under the deepest-protection restriction, and selecting (a,c) does not contradict the depth rule. The new I has only C legal; p118 still assigns P={a},Q empty to that C child.

The actual C continuation at J has two invocations under the checked allowed selection policy. At budget 15 it selects (x,h), with pendants X,W,Y,a,B, and only C cutting h is legal. Its budget-14 child selects (x,a), with pendants X,W,Y, and has no legal branch. This confirms a small C continuation for this witness and supplies no lower bound against the requested runtime estimate.

## Formal source inspection

`HistoryTrace.lean` was opened only after the independent replay. Its eleven propositions are concrete finite computations, importing Std. The numeric label map is a=0,c=1,d=2,x=3,y=4,W=5,X=6,Y=7,h=8,B=9,t=10,d0=11. Its `cut` directly removes each detached singleton from the active F1/F2 trees; the fresh physical replay separately confirms that source normalization performs those root removals within each invocation. The supplied `Top1`–`Top4` are explicit trees rather than results of a universal protected-depth selector. The fresh replay checks that each is the appropriate actual protected-a parent. The credit theorem proves an explicit schedule whose source interpretation is supplied by the p118/p120 checks above; it does not define the full source annotation algorithm.

The original eleven Lean witness statements and two supplemental checks (all twelve initial labels and the explicit protected-a parent tops) compiled successfully. Every theorem's axioms were printed: dependencies are empty or the standard `propext`; no custom axioms, admitted terms or native decision oracle occur. A copied certificate with the final inside-b membership changed to false failed compilation as required. The first audit wrapper incorrectly expected every theorem to be axiom-free; its failed expectation and full output are preserved. The corrected audit permits the standard logical axioms and records the actual `propext` dependency rather than hiding it.

## Scope correction

The first review proposed an unqualified history lemma asserting outside-b placement for all source-reachable qualifying J. This explicit history refutes that proposed lemma. The defect is the passage from equal original F1 depths and greater x depth in F2 to eligibility: analysis P empty does not imply physically unprotected F1. A previous block may reset P while preserving the edge that excludes (x,y) from selection at the new I.

The geometry candidate's stated H2 includes original eligibility and outside-b placement. The new witness violates H2 and therefore leaves the explicitly conditional theorem intact. The original finite local test also imposed outside-b, so its zero-failure receipt remains accurate at its stated scope. The new evidence narrows the route's applicability; it does not falsify the runtime target or establish any asymptotic lower bound.

A complete repair must account for empty-credit block starts with inherited physical protection. One possible replacement obligation is a direct C-prefix certificate for the source-reachable inside-b family, with terminal calls and justified empty-credit exits obeying the exact aggregate allowance. The separate credited A allowance remains necessary. No new universal replacement lemma is accepted here; the supplied witness's C count of two only establishes its own continuation.

## Reproduction

Run `./bootloops-python research/rmaf/thesis_complexity/repair/fresh_review/new_history/replay.py` and then `./bootloops-python research/rmaf/thesis_complexity/repair/fresh_review/new_history/lean_audit.py`. The first uses only the fresh review's independently written evaluator copy and explicit JSON input; the second reads the permitted final Lean source. No parent `history*.py`, `build-history-lean.py`, geometry checker, or separate correctness/transfer implementation was read or imported. The prior review documents, code and receipts remain unchanged.
