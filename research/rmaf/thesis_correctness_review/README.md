# Replay this review

The scripts are one-shot, problem-specific review instruments. They remain beside the review because their purpose is independent evidence for this particular reconstruction. No upstream toolkit code or frozen author results were changed.

- `independent.py` constructs exact directed graphs, enumerates edge cuts and independently enumerates label partitions with disjoint minimal embeddings. Use it to reproduce tiny by-construction controls and the blinded three/four-leaf census. A successful exit means only its named finite equalities passed. `--pilot` and `--full` write receipts; corruptions are required to be detected before comparison.
- `cover_adversary.py` uses the independent graph route to falsify universal raw-cutset `Cover`. Its count concerns local tree/cherry states; it does not count failed algorithm decisions.
- `normalization_domain.py` checks a literal-source counterexample and its passing twin. It deliberately violates active containment and labels that limitation in its output.
- `replay_candidate.py` imports the author algorithm only as the candidate. Its expected decisions come from the frozen independent partition code. `--pilot` times the intended regimes; `--full` checks all n=4 pairs, 150 fresh n=5 and n=6 pairs each, and nine author-selected examples.
- `state_audit.py --limit 120` obtains candidate snapshots and computes optimum cutsets with the independent graph code. Its corruption control was added after the first pilot and is explicitly retrospective. A successful exit concerns only the named sampled normalization constructions.
- `finalize.py` checks source hashes and original receipts, reconstructs fixed source fixtures, and runs the Lean files through `bootloops-lean` from the isolated directory with `LEAN_PATH` unset. It rejects unexpected proof exits or axioms and writes the review summary. The deliberately false Lean file must fail for a mathematical reason.

Run Python from the workspace root with `./bootloops-python research/rmaf/thesis_correctness_review/<script>.py`. The first independent full run follows the stored pilot projection. No script uploads or publishes data. Lean dependencies are restricted to `Std`; `ProtectedBranch.lean` is a retained identical copy of the reviewed source, while `ExistentialRepair.lean` is review-authored conditional logic.
