# Independent address-prefix route receipt

## Scope and grade
Pending. Narrow executable support equality and connectedness only. No G1,
restriction transport, complexity, or novelty claim. Regime 1 fixed statement.

## Frozen controls
CONTROLS.md was written before executable source/proof inspection.

## Sources and tool choice
Pending exact file/line ledger, assumptions, and independent-evaluator rationale.

## Structural derivation
Pending occurrence, root-prefix, and LCA-prefix characterization.

## Executed control and falsification evidence
Pending pilot timing, all exact values, and malformed-case diagnostics.

## Lean verification
Pending fresh dependency compilation and exact kernel-checked statement list.

## Independence and remaining gap
Pending shared source/math/toolchain disclosure and derivation proof limits.

### Source ledger, first entry
Read `research/rmaf/lean/RMAF.lean` lines 8–15, 109–133 (unchanged source).
The executable source defines `Vertex := List Bool` (109), maps child vertices
by cons (111–112), retains the root iff at least one rooted span is nonempty
(116–122), and drops the initial single contributing side in `minimalVertices`
(126–133). Verbatim branch: `if ls.isEmpty then prependSide true (minimalVertices selected r)`.
The following analysis will concern address occurrences; duplicate labels are
permitted by `Tree`, independently of the stronger `Instance` permutation fields.

Toolkit decision (2026-10-14): searched the complete package capability roster
and the external index for Lean/proof-assistant/graph/tree capabilities. No
package supplies this executable tree-address theorem checker; fresh one-shot
prefix enumeration is required by the assigned code-independence check. It
will use only Python standard-library exact lists/tuples/sets, and the local
`bootloops-lean` wrapper for separately stated Lean checks. No existing project
Python geometry or oracle source has been opened.

### Source ledger, second entry
Read `research/rmaf/bridge_review/lean/GraphRegion.lean` lines 9–14 and 85–127.
Verbatim adjacency: `(∃ b : Bool, v = u ++ [b]) ∨ (∃ b : Bool, u = v ++ [b])`.
Verbatim walk constructor: `| step {x y z} : Walk P x y → Adj y z → P z → Walk P x z`.
`ConnectedSupport` requires walks for every member pair (87–91), and
`toRootedRegion` keeps `member := fun v => v ∈ s.first :: s.rest` (106–112).
The original consumer composition is exposed at 123–127. No executable
candidate proof or reviewer implementation has been opened.

### Pilot and launch record
The frozen Python control run preceded the finite sweep: 9/9 exact positive/
empty cases and 4/4 corruptions, including disconnected missing-path output.
The 3-leaf pilot covered 22 binary trees with every 0/1 labelling and all 8
subsets of {0,1,9}: 176 comparisons, generated in 0.047443666 seconds.
The progress unit is an exact actual-source membership comparison compiled
by Lean; Python generation alone does not establish those comparisons.
The intended next layer has 102 trees and 816 comparisons, a 4.64-fold count
increase; its Python generation cost is expected below one second from this
pilot, with Lean compile time still unknown and measured separately first.

Lean pilot compiled all 176 comparisons plus 9 controls and 4 negative
controls in 0.56 seconds wall time (`finite3-build.log`). Scaling only by the
4.64 count factor gives a 2.60 second rough forecast for 816 comparisons,
assuming comparable term size; the larger trees make this a rough planning
estimate, not a runtime claim. The actual 816-case generation took
0.004941042 seconds. Launching this bounded next layer is below the timing
threshold; no larger scan is planned.
