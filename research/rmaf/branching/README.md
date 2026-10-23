# Branching route

This independent route reads the rooted baseline and searches exact small
tree pairs for counterexamples to proposed branching improvements. It does
not import another route's oracle or journals.

## Instruments

- `exact_search.py`: enumerate rooted binary trees, leaf partitions, and
  rooted agreement forests with vertex-disjoint embeddings. Use it to
  falsify forced cherry and endpoint lookahead rules. Output includes exact
  optimum forests, counts, timing, and a scope statement. Its seven frozen
  controls must pass, including deliberately wrong topology, overlapping
  embeddings, and missing or duplicate labels.
- `path_exchange.py`: inspect Whidden two-cut children of reduced baseline
  hard pairs and search a specific overlap-path exchange. Output counts
  actual path states separately. A zero denominator is no evidence.
- `synthetic_exchange.py`: test the same exchange on three-component states
  with fixed blocks of sizes 2,3,2. Their reachability from the baseline is
  not assumed. A surviving finite family is not a theorem.
- `recurrences.py`: use `fractions.Fraction` to certify branching sums and
  isolate each branching root between rational endpoints. It first checks
  the known base 2 for two one-cut branches and rejects a deliberately
  corrupted base 1. It proves arithmetic implications, not safe branching.
- `Certificates.lean`: eight exact integer inequalities, using Lean Std
  and kernel `decide`, with an axiom audit for each theorem. These clear the
  positive denominator for target base 231/100. They are arithmetic only.
- `Mutation.lean`: **intentional compiler failure**, a false arithmetic
  plant. Exclude it from production Lean builds. Compiler rejection is its
  required outcome, retained in the results directory.

These are problem-specific instruments rather than general BootLoops toolkit
packages. The toolkit index was consulted before writing them.

## Replay

```sh
./bootloops-python research/rmaf/branching/exact_search.py --n 6 --quotient
./bootloops-python research/rmaf/branching/exact_search.py --n 7 --quotient
./bootloops-python research/rmaf/branching/path_exchange.py --n 8
./bootloops-python research/rmaf/branching/synthetic_exchange.py
./bootloops-python research/rmaf/branching/recurrences.py
.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean research/rmaf/branching/Certificates.lean
```

The quotient keeps one first tree per unlabelled rooted shape and all labelled
second trees. Every labelled pair can be simultaneously relabelled to such a
representative, so existence of the tested label-invariant counterexamples is
preserved. This argument has not itself been formalized in Lean.

2026-10-14: all instruments first created; upstream toolkit code is unchanged.
