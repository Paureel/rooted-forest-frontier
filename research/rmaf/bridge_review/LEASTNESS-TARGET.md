# Exact minimal embedding of the unchanged extractor

Continue from the completed executable connectivity checkpoint, preserving
all its sources and receipts. Own a new `leastness/` directory and separate
results/progress records. The original executable RMAF definitions stay fixed.

Target: for an actual `RMAF.Tree t` and selection S containing at least one
occurring label, construct `BridgeReview.MinimalEmbedding` whose support is
exactly `RMAF.minimalVertices S t`, whose ambient list is exactly the valid
vertex addresses of t, and whose terminals are exactly the selected leaf
occurrences. Prove ambient membership, inclusion of every selected occurrence,
and leastness among every connected ambient support containing the terminals.
Do not pass those target properties as assumptions. Prove the leaf-address
and label correspondence explicitly, distinguishing arbitrary repeated-label
trees from the unique-labelled `RMAF.Instance` case.

MAY ASSUME: the audited executable connectivity/nonemptiness theorems and
GraphRegion/PureBridge graph lemmas with their hypotheses. MAY NOT ASSUME:
extractor-to-prefix-hull equality, leastness, terminal preservation, correct
ambient interpretation, or cross-tree address transport. The earlier prefix
arm proved generic hull connectivity; its universal extractor equality is
only a written argument. A generic hull theorem alone does not close this
target. Do not depend on unfinished triple-family work or change its files.

Frozen controls before proof construction: the quartet crossing support,
singleton, sibling pair with omitted initial root path, empty and absent
selection, singleton-root tree, duplicate labels and duplicate selection,
and the deep initial-path suppression case. Controls must kill deleting an
intervening path vertex and adding the input root above the selected LCA:
the latter stays connected but violates leastness. Also reject a support
containing an invalid ambient address and one missing a selected terminal.
Keep true twins and a malformed-proof diagnostic control.

Follow prove-protocol: adversary first, then independent prefix/LCA and
edge-separation routes, fresh nonauthor use-site review. Reusing completed
agents is appropriate; never duplicate or steer an active proof agent, and
wait for capacity rather than exceeding the shared concurrency limit. While
waiting, pin exact statements, controls and source contracts without claiming
closure. Lean-check proved universal claims, retain failed attempts and
standard-only axiom receipts. Finite cases and ordinary prose derivations
must remain separately labelled.

Acceptance is an actual exact-source MinimalEmbedding constructor and a
kernel-checked call to its existing region/consumer interface. Restriction
and suppression transport between trees, G2-G7, pure-bridge exchange and
the faster bound remain separate debts. At most two active child agents;
fresh agents use Astra xhigh. Keep artifacts local, dashboard writes atomic,
metrics objects and lemma records with id,label,status,detail. Root owns the
aggregate theorem count. Suggested paths: results/bridge-leastness-* and
progress/bridge-leastness.json under research/rmaf/.
