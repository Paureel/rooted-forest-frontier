# Read ledger

Source opened: `research/rmaf/sources/baseline/whidden-thesis-2013.txt`, local thesis PDF extraction; rendered source pages 110 and118 also viewed. Locators below use printed thesis pages. No bibliographic entry added and no novelty claim made.

| Read claim | Locator | Source wording / extraction |
|---|---|---|
| Unary labelled rho convention | Ch2 p12, PDF25, text820–829 | “we augment the tree with a labelled root node”; its only child is the original root. Unlabelled nodes with fewer than two children are suppressed. |
| Active roots and trivial reductions | p104, PDF117, text5700–5740 | Rt partitions leaves by active ancestor; root components leave Rt; common F1/F2 sibling pairs are replaced in Rt by their parent. |
| Cut legality and protection inheritance | p107, PDF120, text5857–5870 | “only if Ei does not contain any protected edge”; the separate root-sibling exclusion is on the same page. A surviving suppressed edge inherits protection from either replaced edge. |
| A2BC protection differs from A3BC | pp107,109, PDF120,122 | A2BC's C branch protects its first endpoint and both pendant edges; A3BC's C branch protects only its first endpoint. The protected-second-endpoint A2BC order is B then A. |
| Priority and special branches | pp109–111, PDF122–124; p110 rendered | RB, RB*, 2B and BCY precede A2BC/A3BC. BCY's second cut set is {e_c,e_y}; y is the protected uncle's F2 sibling. |
| Depth choice | pp110–111; p110 rendered | Restrict to descendants of the deepest protected-edge top; choose greatest F1 depth; at ties prefer disconnected endpoints, then greatest deepest-member F2 depth. |
| Exact induction expression | p117, PDF130, text6284–6294 | `I(k,P,Q) <= alpha(2^(k-|P|) + |Q| 2^(k-|P|-1)) + |P|-3`. Its cap-two declaration is not used by this route. |
| Local original geometry and group hypotheses | p118, PDF131 rendered, Figure6.6 | e has height at most two below the original great-grandparent region; the source's stated later-group/empty-credit induction is read literally as a conditional premise. |
| G4 union annotation and exception | p123, PDF136, text6514–6531 | Union original P',Q' into G4.2/G4.3; in G4.1 A3BC set B-child empty and C-child P' union{x},Q' union{x}. |
| Two-protected path case split | p121, PDF134, text6409–6446 | Connected pair analysis splits the outside-LCA and inside-pendant cases; BCY excludes the protected uncle as an immediate child of the first pendant. Used as a source guide, with its renamed argument written out in PROOF.md; not assumed as a proved source lemma. |

Read as supplied witnesses, not held-out proof: shared `repair/controls-frozen.json`; nine-leaf and thirteen-leaf result JSON. Their values were known before authoring the checker, so reproduction is a control, not independent certification of the candidate proof. The earlier `local-repair.md` was read as a proposed two-root argument.

Provenance boundary: no adversary implementation/proof plan, parent implementation, recurrence-arm document/code, correctness/transfer implementation or proof was read. Shared source definitions and frozen witness JSON are the deepest common inputs across routes. The current route's own numerical search cannot certify its own source-geometry proof.
