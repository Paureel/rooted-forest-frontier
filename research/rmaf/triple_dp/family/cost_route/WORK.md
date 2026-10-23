# Cost-route work journal — 2026-10-14

State: OPEN. Forced-distinct proof arm, indexed families and distinguished-open assembly.
Target read first: `../../FAMILY-TARGET.md`. Parent reports X0 NO-FIRE.

## Pinned claim
Construct actual finite indexed families of nonempty leaf-labelled path-convex supports with pairwise disjoint support, coverage, and at most one root-containing open support. Seek disjoint-union closed assembly first, then one distinguished open-component extension/merge if time permits. Count and closing-cost claims must follow from constructed index families rather than a hypothesized block correspondence.

## May assume / exclusion
May use audited `ConnectedRegions.lean` and `TripleDP.lean` with their printed hypotheses, Lean Std. Do not read new author or other route family code/proofs. Do not assume trimming, family assembly or cost preservation. No sorry, custom axioms, native_decide, or raw-support bijection claim.

## Controls frozen before construction
T1: binary cherry with two leaf singleton child families. Keep-both-closed parent family has two distinct indices, covers both leaves, root unused, cost 2.
T2: same cherry, merge the two distinguished open singleton regions through the root: one region, cost 0 while open and 1 upon closing.
T3: one-sided extension of left singleton through parent root plus separate right singleton: two regions, one open, one closed; closing cost increment 1.
T4: adjacent regions of identical label/color metadata remain separately indexed under keep-closed assembly; cardinality stays 2.
T5: root/singleton boundary with one labelled support: count 1, open cost 0, closing increment 1.
Regression-only controls: gapped LCA-closed support, leafless-child-incursion pair, unused internal vertex. These must be handled explicitly in interface/debt notes, not counted as fresh holdout.
Mutant M1 (false proposition): keep-both-closed assembly of the two singleton child families has block count 1. Require Lean proof attempt to fail at the proposition, with the otherwise identical true block-count-2 twin accepted.
Additional structural mutant M2: automatically merging adjacent same-color regions preserves block count. Kill with T4; do not identify indices by color.
No census planned. Initial Lean startup/typecheck is the timing pilot; retain elapsed time and logs.

## Tools consulted
Read toolkit index; no listed package supplies tree-support family assembly. Existing Lean proof modules are allowed dependencies; new Lean file is problem-specific formal mathematics, not a general instrument. Read relevant engine wrapper and local existing module before construction.

## Construction ledger
Pending.

## Executed evidence
Pending.

## Acceptance/interface debts
Fresh semantic/axiom/control review remains required. Parent handles independent review and trimming. This arm does not close full G2; restriction, graph-to-DP, source-color synchronization, and consuming interface are separate until explicitly established.

## Process note
Supporting skill instructions were read before this skeleton was materialized; no mathematical construction or other-route source was read before the skeleton.

### Supporting module read — before construction
`ConnectedRegions.lean` supplies path convexity, prefix closure equivalence for root-containing regions, and rooted child decomposition. `TripleDP.lean` supplies `BTree`, addresses, and the concrete four transition forms in `badRules` (close both; extend left; extend right; merge). No new family module was opened. Current implementation plan: finite index enumerations plus supports; sum indices for close-both; cost = enumerated block count minus the actual root-containing boundary charge. Start with closed union, which is already an acceptable universal partial assembly result.

### Construction completed for three transitions
`FamilyAssembly.lean` now constructs closeBoth, extendLeft and extendRight,
each with finite enumeration, geometry, nonempty leaf labels, disjointness,
coverage, and exact root-boundary membership. Each has an actual cardinality
and cost theorem. `cost_counts_closed_indices` and `mem_closedIndices_iff`
prove cost counts precisely the root-absent indices. Per-index label-set
preservation is proved for closed union and root insertion.

No family construction or cost-preservation premise was imported. The
adjoinRoot helper assumes only convexity of its one enlarged support; the
one-sided transition constructors prove that premise from the old child's
convexity and actual child-root membership. Imports remain the two allowed
old modules and Std. Original sources/results were not changed.

### Executed evidence
Final replay command: `./bootloops-python research/rmaf/triple_dp/family/cost_route/replay.py`.
Retained receipt: `../../../results/triple-family-cost-replay.json` (actual
workspace path is research/rmaf/results/triple-family-cost-replay.json).
Verbatim terminal summary:

```
PASS: 6 declared replay stages; 2/2 false propositions rejected and 2/2 clean twins accepted.
Scope: three actual-family assembly constructors; independent acceptance and full G2 remain open.
```

The final receipt retains compiler version, exact elapsed durations, return
codes, axiom sets and source SHA-256 digests. Dependency startup pilot was
under one second; each later compilation was also under one second. No
extrapolated long run or finite census was used. Intermediate proof
scripts failed elaboration and subsequent repaired source passed; all
iteration logs remain in results/triple-family-cost-*. Only the final replay
is the theorem/control receipt of record.

### Control interpretation / amendment
T1, T3, T4, T5 traverse the actual universal constructors. T2 is a manually
constructed positive merged-family fixture; it supplies no universal merge
evidence. The final same-color fixture strengthens the initially repeated
value fixture by using distinct leaf values (0,7) and (1,7), with shared color
7; its expected cardinality remains the frozen 2. Earlier repeat-value logs
are preserved. M1 and M2 still change only cardinality 2 to 1 in the matching
positive twins and are each rejected by actual false-proposition diagnostics.
The gapped and incursion controls are old regression evidence, not holdout;
the incursion check proves only the stated address-predicate label equality
and support distinction, not a full-family normalization theorem.

### Final producer grade / debts
CLOSED-UNVERIFIED for the three assembly constructors. Fresh nonauthor review
has not been performed by this arm. Whole G2 OPEN. Still missing here:
universal merging, restriction/completeness, trimming, leafless-fragment
discard, color/mask legality, DP-state/rule and graph correspondence. The
family model covers all leaves of its supplied tree; a strict relevant-leaf
subset adaptation is not silently supplied. Parent owns broad acceptance
and independent verification. No other route's new source was read.
