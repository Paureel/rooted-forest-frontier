# Source and independence ledger — 2026-10-14

Read source: `research/rmaf/sources/baseline/whidden-thesis-2013.txt`, locally retained primary thesis text, printed pp.12–18 (PDF pp.25–31), pp.101–103 (PDF pp.114–116), pp.112–116 (PDF pp.125–129). No sibling edge-route files, original proof/implementation, or reviewer code have been opened. Only filenames from a repository inventory were seen.

Read facts, with exact short source strings:

- p.12: “we augment the tree with a labelled root node” whose only child is the original root. Minimal connecting subtrees are reduced by suppressing unlabelled nodes with fewer than two children.
- p.15: “a forest F is an agreement forest (AF) of F1 and F2 if it is a forest of both F1 and F2.”
- p.16: “we say that a exists in F2 if there is a node a1 P F2 such that F a” (the line-broken formula continuing on following source lines equates the two entire descendant subtrees). The sibling notion therefore permits compound subtrees, not just ordinary labelled leaves.
- p.17: “there are no two leaves a and b such that a „ F2 b but a  F1 b.” The source says intermediate algorithm forests maintain this component containment.
- p.18, Lemma 2.4: block containment, no overlap, and compatible rooted triples characterize being a forest.
- pp.101–102, Lemma 6.5: E is any edge subset producing an AF of the original trees; E2 is a subset of E producing the sibling condition; E1 is every E edge on the a-to-c path; no condition forbids cuts inside compound a or c.
- p.102 proof: “there exists a leaf x1” inside the union of the two sibling subtrees and connected to u after E. This is a test target, not an assumption.
- pp.112–113, Lemma 6.10: the first exchange applies to (a,c); the second explicitly applies to (x,u), with u the entire newly reunited subtree. Restricting a theorem to ordinary leaves would not establish that second use.
- p.116, Theorem 6.12: its exchange removes ec and adds the pendant cuts eb1, eb2, in an optimum extension E0; the source's sibling definition remains compound-capable.

Inference under test: allowing E to erase all labels below a compound sibling may invalidate the p.102 surviving-label assertion even with active component containment and genuine AF compatibility. This is not a source-attributed result.

Toolkit consultation: `bootloops/tools/README.md` was read; its available packages do not provide a rooted agreement-forest leaf-partition and minimal-embedding evaluator. The external `phyloexact` mention concerns phylogenetic probabilistic models, not this combinatorial predicate. A one-shot local evaluator is justified by the independent-author requirement and will not reuse the existing original/reviewer implementations.

Controls are the parent-frozen `repair/controls.json` and are development controls, not held-out certification. All exact comparisons will be tested with corrupted expectations before adversarial search. Shared layers with other routes are only the primary definitions, unary-rho convention, and frozen fixtures; no claimed computational independence extends to those shared assumptions.
