# Main algorithm target

Priority amendment, 2026-10-14. The user's original faster-algorithm objective is the main work. The later thesis audit is secondary. All earlier sources, proofs, results and failed formulations remain preserved.

The deliverable is an explicit exact algorithm for ordinary rooted binary MAF, a complete correctness and termination argument, and a rigorous bound O*(c^k) with c < the audited 2.3391 benchmark. Here k is the optimum number of components and the initial cut parameter is q=k-1. No added rho leaf is implicit. A new algorithm and a repaired prior algorithm are different provenance claims.

## Three milestones

1. **Complete algorithm:** executable rules, their priority and applicability tests, terminal cases, witness reconstruction, and a defined action for every input/state. Every proposed acceleration must name its call site and its fallback. A faster solver for a restricted family is only one subroutine.
2. **Exactness:** every returned forest is valid and at least one optimum survives each reduction/branch cover. Prove the graph/state correspondence and termination. Finite optimum comparisons test the implementation but do not prove universal coverage.
3. **Exponent:** account for every emitted child, preprocessing/search cost, local optimizer, reconstruction and parameter conversion. Derive a recurrence or a global charging argument with a strictly smaller base. Smaller kernels or faster sample runs alone do not establish this milestone.

All three milestones are OPEN. The existing supporting Lean inventory is not a completion percentage.

## First concrete candidate family

Use the ordinary-convention split-or-decompose algorithm as an explicitly attributed scaffold. Attack its limiting branching vector (1,1,3,4,4), audited in `branching/open-lemma.md`. The first candidate is a total replacement macro for its hard two-pendant-cut child, with an explicit optimum-preserving cover and charged residual decreases.

Previously pinned sufficient residual vectors are (2,2,2), (1,3,3), and (1,2); combined with the original two unit branches, their arithmetic passes c=231/100. Existing Lean certificates prove only those arithmetic inequalities. Coverage, rule construction and the full algorithm proof remain open. Other macro sizes or measures are allowed, provided exact weighted mass and generation cost are pinned before accepting them.

The immediate experiment must use actual reduced hard children and a separate exact partition/embedding oracle. It must test the already rejected forced-cherry and endpoint-bonus ideas, detect a deliberately incomplete branch cover, and reject a false recurrence. Empty, singleton, identical-tree, root, suppression and component-count controls are mandatory. Known witness data live in `results/branching-search-n6.json`, `results/branching-search-n7.json` and `results/branching-recurrences.json`; extract literal expected values from these receipts rather than from this prose.

After controls, synthesize and falsify whole macros or candidate measures against exact optimum preservation and rational branching mass. An optimum oracle is a test instrument and cannot be a step in the proposed algorithm. Keep development and fresh verification implementations separate. Measure a small pilot before extending a census.

## Forced-distinct routes

- **Branch macro/state route:** complete local cut rules or state-sharing/measure changes for the actual bottleneck, including exhaustive coverage and all residual costs.
- **Decomposition/cover route:** a complete safe-cover generator into the pure-bridge or compatible/triple terminal classes, including cover size, optimum survival, paid precuts and every local-query budget. Exact restricted completion alone gives no unrestricted improved exponent.

Stage a separate X0 adversary before proof construction, then these named routes in fresh contexts without cross-reading unfinished work. A nonauthor verifier must reconstruct the successful algorithm, freeze and execute controls, review every consuming hypothesis, and replay the Lean proofs before accepting a result. Use GPT-6.1 Sol with xhigh for newly dispatched research agents, as requested by the user.

## Supporting work admission

Use existing degree-two, family/restriction and DP results only at named algorithm call sites, with their exact hypotheses and retained review receipts. Pending or conditional graph/automaton/implementation interfaces remain open. Do not start another supporting-lemma campaign until the candidate algorithm identifies the missing statement and explains how it changes coverage or the exponent.

Do not resume standalone thesis correctness/runtime repair rounds. Retain their finite counterexamples and scoped results for reuse where a concrete candidate requires them. The source-reachable inside-b witness does not refute the thesis's speed bound.

## Reporting

The primary dashboard card reports the three milestones above, the current candidate, its exact missing coverage/complexity obligation, and newly executed evidence. Separate proved Lean statements, reviewed prose, finite tests and conjectures. No improved bound or novelty claim is accepted merely because a process succeeds. Keep hosting, artifacts, compute and previews local.

If a candidate fails, preserve its smallest measured counterexample, identify the mechanism, and change the algorithm or organizing route. Do not repeatedly strengthen a killed lemma without evidence that its new premises are enforced by the actual algorithm.
