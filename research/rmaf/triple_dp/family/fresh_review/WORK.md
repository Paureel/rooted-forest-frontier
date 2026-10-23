# Fresh normalization review

The review is limited to raw-to-retained family normalization. The first source
read was `../../FAMILY-TARGET.md`, followed by `../INTERFACE.md`,
`../controls.json`, and `../controls-amendment-v2.json`. No author implementation
or cost/path route proof was read before writing `direct_controls.py`.

The tiny checker reconstructs an undirected graph from each nested binary tree,
finds unique paths by breadth-first search, and takes their vertex union. It
imports no RMAF or author helper. Its only shared semantic inputs are the frozen
interface, the frozen controls, and binary-address labels. These are known
registered controls, not holdout cases. The comparison is exact, and any unequal
registered field fails the run. A deliberately wrong singleton cost must be
rejected by the same comparator before control replay; its clean twin must pass.

The BootLoops package and capability indexes were consulted: no indexed package
implements this tree-family interface, and reusing the author's checker would
defeat the requested independent implementation. This script is a one-shot
review instrument, retained here with its receipts rather than added to the
general toolkit.

Runtime is initially unknown. The singleton plant is the bounded timing pilot;
only the registered controls are then replayed. No larger census is authorized.
Lean modules will be copied to a review-owned source snapshot and rebuilt with
the workspace `bootloops-lean`, `ELAN_HOME`, and a review-only `LEAN_PATH`.
The false proposition must yield the actual `0 = 1` diagnostic, with a clean
singleton twin compiled under the same configuration. New-family declaration
audits and imported dependency audits remain separate.

Expected remaining obligations: path-union/graph correspondence, transition
restriction/assembly and its charge accounting, color/mask state decoding, and
Python extraction correctness. Their exact boundary will be checked after
rebuilding the normalization modules. Full G2 is not graded by this review.

## Execution record

The direct checker passed all 17 registered rows. Its singleton pilot took
0.000014834000467089936 seconds; the complete tiny replay took
0.0006432089994632406 seconds. Both are recorded in
`results/triple-family-fresh-direct-controls.json`; neither measures a search
or establishes a scaling law. `pre-author-read.sha256` retains the checker
and control hashes from before author-source inspection.

The isolated source replay compiled the positive modules and recorded all
31 author-family axiom queries and 27 dependency queries in
`results/triple-family-fresh-lean.json`. The false proposition failed at
`0 = 1`; its same-import clean twin passed at `0 = 0`. Three supplementary
reviewer consequences compiled separately, with their own receipt
`results/triple-family-fresh-supplement.json`. No broad package suite or
larger census was run.

The semantic report is `REPORT.md`. A further fresh Astra xhigh agent was
assigned its scope and prose review under the explicit fresh-context
requirement in referee-sim; this agent is restricted to the normalization
sources and review receipts. The cost and path proof routes remain unread
and uncredited by this review.
