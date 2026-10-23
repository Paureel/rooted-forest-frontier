# Component/partition route

This one-shot evaluator independently reconstructs the yielded forest after cuts and recognizes agreement by its leaf partition, induced rooted subtree signatures, and pairwise vertex-disjoint minimal embeddings. Nodes retain original tree identities; an active edge is identified by its bottom endpoint, even after unary suppression. `normalized` only edits current edges and never invents an incoming edge at a component root.

Use it for the frozen repair controls, explicit compound-subtree adversaries, and small structural root-boundary cases. It does not replay the algorithm, assert reachability of every structural state, or establish a universal theorem.

Output is exact Boolean and finite-set evidence. A successful process means its assertions passed; it does not mean normalization is universally correct. The pilot intentionally reports a failed normalization with all stated target hypotheses true.

Run using the project launcher:

```sh
/Users/paurel/Documents/ChatGPT/bootscience/bootloops-python /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/component_route/evaluator.py --stage controls
/Users/paurel/Documents/ChatGPT/bootscience/bootloops-python /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/component_route/evaluator.py --stage pilot --limit 40
```

Acceptance requires all four parent-frozen fixtures, four corrupted-expectation catches, and a zero-cut identity control before adversarial instances. A fresh nonauthor reconstruction is still required for certification. No original/reviewer evaluator, proof, or sibling route code was read or imported. The dependencies are the Python standard library, source definitions, and the frozen controls.

2026-10-14: created as a deliberately independent problem-specific instrument. Toolkit index consulted; no general rooted-AF component/embedding checker was available there. Existing campaign evaluators were deliberately excluded to protect this route's independence. No upstream tool changed.

## Restricted construction

The second stage is pinned in `PROOF-TARGET.md`. `narrowed_adversary.py` imports only this route's evaluator and tests the conditional surviving-fragment statement plus the strict empty-common-subtree repair. It uses current reduced forests and does not implement the remaining original-edge translation. `PROOF.md` contains the proposed partition argument and traces both Lemma6.10 exchanges, including compound u, and Theorem6.12's final exchange.

Executed commands:

```sh
/Users/paurel/Documents/ChatGPT/bootscience/bootloops-python /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/component_route/narrowed_adversary.py --n 4 --limit 0 --name narrowed-n4-full
/Users/paurel/Documents/ChatGPT/bootscience/bootloops-python /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/component_route/narrowed_adversary.py --n 5 --limit 20000 --name narrowed-n5-bounded
/Users/paurel/Documents/ChatGPT/bootscience/bootloops-lean /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/component_route/EmptyRoot.lean
```

The deliberately false `EmptyRootNegative.lean` must fail compilation. Do not import it into any production proof. The six named positive Lean lemmas concern binary root fragments and exact exchange arithmetic. The agreement-forest proof remains a proposed prose argument, and `REVIEW-REQUEST.md` lists the outstanding fresh-review requirements. The dashboard checkpoint and `component-proof-summary.json` distinguish these statuses.

2026-10-14, second stage: added and ran the narrowed falsifier after freezing its target, then constructed the partition proof. Earlier evaluator and adversary receipts remain unchanged. No external evaluator or sibling route was read.
