# Independent path-geometry route

Target first read: `../../FAMILY-TARGET.md` (2026-10-14).

Claim under investigation: trimming a nonempty leaf-labelled path-convex open support to its label span plus root stem excludes excursions into any child subtree containing no label of that support.

Allowed sources: target, audited `ConnectedRegions.lean`, original `TripleDP.lean`, toolkit and skill instructions. New author family files and other route code are excluded.

Expected proof boundary: one universal trimming/path lemma only. Family restriction/assembly, complete G2, executable RMAF extraction, and source suppression remain OPEN.

Controls and a false-proposition/positive twin will be frozen before proof code.

## Source and method ledger

Read `ConnectedRegions.lean` and original `TripleDP.lean` only. Load-bearing
retrieval: `rooted_pathConvex_iff_prefixClosed`, with hypothesis `root : region []`.
Read BootLoops tools index: no package provides symbolic Lean tree geometry;
this is a problem-specific extension of the accepted address lemmas, not a new
general toolkit instrument. Compiler: project `bootloops-lean`, Std only.

Skills applied: prove-protocol, tool-stewardship, acceptance-gate,
independence-bookkeeping, planted-truth, timing-discipline, reading-contract.
Controls below are author-owned construction/regression checks; they cannot
serve as a fresh independent reconstruction. Parent campaign owns external
semantic/axiom/control review. No larger census is planned. Compiler runtime
is unknown until measured; compile the tiny controls first, then dependencies.

## Frozen claim (before proof code)

For any address support R, any actual leaf predicate L, and any root-containing
path-convex R, put C(v) iff there exists a such that L(a), R(a), and v is a prefix
of a. Then C is path-convex, C is a subset of R, C has exactly R's L-labels,
and C contains the root iff R has an L-label. For every child side s, C has a
vertex in child s iff R has an L-label in child s. Thus a nonempty open region's
root-path trim has no leafless child incursion. Pairwise disjointness survives
simultaneous such shrinking. Actual finite labelled binary trees are pinned by
BTree with recursive vertex and leaf address lists; labels occur only at leaves.

This addresses the open root-path trim. Equivalence to the separately phrased
minimal unrooted span plus its stem, closed-region trimming, the four transitions,
and block/closing-cost preservation are additional links unless proved below.

## Frozen exact controls (2026-10-14, before code)

Use 0=false, 1=true, epsilon=root. Tree T has leaves 00,01,10,11; all prefix
vertices epsilon,0,1,00,01,10,11. Labels are the leaf addresses themselves.

R0={epsilon,0,00}; R1={epsilon,0,00,1}; both are path-convex and have sole
label 00; both trims must equal R0, removing leafless child incursion 1 from R1.
This known pattern is regression, not holdout. G={epsilon,00} must be LCA-closed
but fail path-convexity at missing vertex 0 (also regression).

Independent authored control T2 has leaves 0,100,101,11 and vertices
epsilon,0,1,10,100,101,11. R2={epsilon,1,10,100,11,0} has labels 0,100,11,
so 0 must remain; R3={epsilon,1,10,100,11} has labels 100,11 and must remain
unchanged. The distinction catches accidentally treating every opposite child
as dispensable. Singleton tree has sole root label and trim {epsilon}; empty
label set gives empty trim, and is discarded rather than charged. Family
supports {0,00} and {01} in T have adjacent same-color blocks, stay disjoint and
separate; vertex 1 is unused. This is only a control of shrinking and block
identity, not an assembly theorem.

Wrong proposition diagnostic: in T, path-convex rooted R1 has an occupied
1-child, therefore it has a labelled leaf in that child. A Lean `by decide`
proof of that concrete false proposition MUST fail, and its exact negation
(clean twin) MUST compile with the same dependencies. Also the positive claim
that the trimmed R1 has no vertex in the 1-child MUST compile. Any unexpected
success of the false file or failure of the clean twin is a control failure.

Acceptance: exact compiler exit and diagnostics retained, fresh compilation of
allowed dependencies into own output directory, theorem axiom printout without
sorryAx, and no claims beyond formal signatures. All examples are revealed to
this author and hence are construction/regression controls, not holdout.
