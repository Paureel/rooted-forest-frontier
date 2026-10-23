# Branching route journal

2026-10-14: Read spec.json. Independent route initialized. No improved theorem claimed. Next: read applicable protocols and the full rooted algorithm section.

## Baseline read — arXiv:2409.18634v2 (21 March 2026)

Opened the full HTML rooted section §6, including every proof in Lemmas12–16 and Algorithm rMAF/Figure16; also read §2 rooted/forest definitions, §3.2, and §§4.1–4.2. Locators are section/lemma identifiers in https://arxiv.org/html/2409.18634v2. These are retrieved facts, not newly proved results.

- §2 footnote2: the paper does not require root-augmentation taxon rho; claims its algorithm works with or without it. k in theorem is component count; the recursive decision budget is further cuts (§3 preceding §3.2), so initially k−1 cuts.
- §3.2 Whidden(t=2): 2T(k−1)+T(k−2). For t=1, a deterministic pendant-edge cut is safe; t≥3 gives ≤2.206.
- §6 Lemma13: special disjoint/homeomorphic cases have worst recurrence T(k−1)+3T(k−2), root ≤2.3028.
- §6 Lemma16: the two-cut Whidden child is bounded by T(k−1)+2T(k−2); hence overall 2T(k−1)+T(k−3)+2T(k−4). This is the unique maximum among the printed rule families.
- Lemma16 proof Cases1–2 (triple-overlap and overlap-chain) allocate a one-cut branch and then two branches of cost two. Stronger handling of these cases is a possible target, but not established.

## Instrument choice

Consulted bootloops/tools/README.md in full. Existing packages are integration, algebra, or phylogenetic likelihood instruments, not an exact rMAF combinatorial oracle. This route needs a new small-instance partition evaluator, kept as a problem-specific independent checking instrument; Python fractions suffices for exact recurrence inequalities.

## Frozen controls before candidate search

1. Identical trees ((a,b),(c,d)): one-component agreement forest accepted; incompatible one-block forest for ((a,b),c) versus ((a,c),b) rejected.
2. Distinct rooted triplets: optimum=2 by construction, e.g. ({a,b},{c}) for T=((a,b),c), T′=((a,c),b).
3. Singleton partition always accepted for equal leaf sets.
4. Deliberate overlapping partition for T=((a,b),(c,d)): ({a,c},{b,d}) must be rejected despite equal induced two-leaf restrictions.
5. Duplicate label / missing label partitions rejected; clean twin passes.
Candidate A: claim every t=2 cherry has some optimal forest retaining the cherry together. Search n=4 then n=5; exact counterexample kills the deterministic two-pendant-cut replacement.
Candidate B: claim isolating one endpoint of a t=2 cherry in a reduced tree pair forces a one-cut deterministic rule before another all-t=2 hard pair. Search structurally for a reduced child with only t=2 cherries; finite survival is not proof.
Pilot units: exact tree pairs checked and witnesses accumulated; first n=4 stage timed before larger stages.

## Executed exact search

All scripts were run with ./bootloops-python; machine timing is the script's monotonic-clock measurement. No other route's solver was imported.

| Stage | Tree pairs scanned | Time (s) | Outcome |
|---|---:|---:|---|
| n=4 full | 225 | 0.00957 | Forced cherry retention refuted without baseline-rule exclusions. |
| n=5 full | 11,025 | 0.85216 | Endpoint lookahead refuted for classical t-only exclusions. |
| n=6 quotient | 5,670 | 0.16248 | Forced cherry retention refuted even after Figure16 steps2a–d exclusions. |
| n=7 quotient | 114,345 | 3.37652 | Endpoint lookahead refuted even after all earlier Figure16 tree-pair rules. |

The n=4 pilot justified n=5; the simultaneous-label quotient reduced the next stages rather than multiplying a long full scan. Frozen validity controls: 7/7 each run. Retained wrong-topology, overlapping-embedding, duplicate-label, and missing-label catches.

Candidate A killer: research/rmaf/results/branching-search-n6.json, forced_cherry_baseline_hard_counterexample. Exactly 3 components are optimal, but every forest retaining the selected t=2 cherry needs at least 4. This disproves a deterministic pendant-cut replacement even with the earlier printed rules unavailable. It does not refute choosing a different cherry or a more complicated macro.

Candidate B killer: research/rmaf/results/branching-search-n7.json, endpoint_lookahead_baseline_hard_counterexample. Isolating one selected endpoint leaves another reduced pair where the earlier printed rules are unavailable. This disproves the universal extra-cut credit for every endpoint branch. It does not refute adaptive selection or a weighted measure with an independently proved invariant.

After two dead candidates, switched from informal optimism to mechanical state search and a precisely pinned residual macro hypothesis (open-lemma.md).

## Overlap-path exchange search

Baseline-reachable child scans: n=7 inspected 114,345 tree pairs and 252 eligible Whidden children; n=8 inspected 3,108,105 pairs and 2,670 children, in 29.78996s. Both found ZERO path-overlap states. These zero denominators give no evidence for the proposed exchange. n=8 was projected from the n=7 pilot; no larger scan was launched.

Restructured to synthetic three-component states of sizes 2,3,2. A 1,000-tree evenly spaced pilot yielded 186 exact path instances in 0.22562s; full search gave 2,640 instances over 10,395 trees in 3.35172s, no counterexample. This is finite survival only, with baseline reachability explicitly unproved. The next frozen family is described in open-lemma.md.

## Exact recurrence certificates

Script-of-record: recurrences.py; output: results/branching-recurrences.json. The known two-one-cut-branch base2 control passes; corrupted base1 is rejected. Exact rational root isolation brackets the published bottleneck between 2.339057129 and 2.339057130. This is merely recovering the printed recurrence's root, not a scientific improvement over the rounded 2.3391 headline.

At c=231/100, verbatim script summary:

    published_bottleneck 2896278200/2847396321 False
    conditional_macro_a 921759400/949132107 True
    conditional_macro_b 642840264200/657748550151 True
    conditional_macro_c 2796278200/2847396321 True
    lemma13_worst 5900/5929 True

Every other printed branching family also passes. The conditional target is a structural macro rule replacing residual vector (1,2,2) by (2,2,2), (1,3,3), or (1,2), under the exact hypotheses in open-lemma.md. No safety proof or rule generator exists yet.

## Lean kernel checks

Executed .runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean branching/Certificates.lean (full workspace path in README). All eight integer inequalities compiled. The #print axioms output says each theorem does not depend on any axioms; retained verbatim at results/branching-lean-certificates.txt. This establishes arithmetic only. Neither an rMAF reduction nor the complete algorithm or recurrence theorem is formalized in this module.

A deliberately false certificate in Mutation.lean was compiled separately and REJECTED with exit1; results/branching-lean-mutation.json retains the error. It is a controlled-failure fixture, excluded from production builds.

Self-grade: OPEN for the improved algorithm, finite candidate refutations with fresh independent verification pending; Lean kernel-checked arithmetic certificates only. No novelty claim.
