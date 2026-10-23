# Pinned semantic vocabulary and proof obligations

Names proposed in namespace `LeastEmbedding`. These definitions recurse on the unchanged `RMAF.Tree`; they do not alter it.

- `vertices : Tree → List Vertex`: a leaf contributes `[[]]`; a node contributes `[]` followed by `prependSide false (vertices l)` and `prependSide true (vertices r)`.
- `terminals : List Nat → Tree → List Vertex`: a leaf contributes `[[]]` exactly when its label belongs to the selection; a node concatenates the two side-prefixed terminal lists. No root is inserted at an internal node.
- `ValidVertex t v`: inductive actual node-occurrence relation (root at every t, left/right extension).
- `LeafOccurrence t v x`: inductive actual leaf-occurrence relation (a leaf labelled x at [], left/right extension through nodes).

Required semantic lemmas: vertices membership iff ValidVertex; terminals membership iff there exists an actual LeafOccurrence with selected label; `x ∈ leaves t ↔ ∃ v, LeafOccurrence t v x`; every leaf occurrence is a valid vertex; uniqueness of the occurrence address when `(leaves t).Nodup`; derive that nodup premise and exactly-one-address interpretation from each RMAF.Instance permutation field. Repeated labels in arbitrary trees are permitted and may select multiple addresses.

Required extractor lemmas, without importing unproved hull equality: every rooted-span vertex has a selected terminal descendant; minimalVertices preserves every terminal and stays in vertices; every common ancestor of all selected terminals is a prefix of every minimalVertices vertex. The last two prefix facts imply leastness using any connected competitor's existing RootedRegion: its root is a common ancestor of the terminals; convexity forces every minimal vertex into the competitor.

Final constructor: for an actual selected leaf occurrence, use completed `ExecutableBridge.extractedSupport`; set ambient exactly to vertices t and terminals exactly to terminals S t; fill terminal_nonempty, inAmbient, containsTerminals and minimal from new theorems. Preserve support membership exactly. Instantiate MinimalEmbedding.region and its existing deepest-root consumer under their unchanged depth/overlap hypotheses. Equal addresses from different trees do not establish a correspondence between them.

This is a proof plan, not a proved result. No closure is claimed before adversarial execution and kernel checks.
