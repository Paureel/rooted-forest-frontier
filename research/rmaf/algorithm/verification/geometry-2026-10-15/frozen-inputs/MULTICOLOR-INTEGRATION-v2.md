# Joint vertex ownership integration target v2

Proposed complete-macro organizing change for c=233/100. All structural
statements below are OPEN, to be falsified and formalized before use.
The multi-color X0 tests source cores independently; it does not certify
these graph-to-core interfaces or the remaining scaffold.

Use target VERTICES rather than require a shared EDGE among three parent
embeddings. Three pairwise-intersecting tree subtrees have a common vertex,
but need not have a common edge. This avoids importing that stronger premise
without its actual hard-child proof.

## Connected three-parent macro

If all three parent embeddings meet a target vertex v, select each possible
survivor in turn. For each other parent D, color its labels by the nonempty
leaf regions of T[D] minus v; every final D-piece must be monochromatic to
avoid v. An overlap vertex is unlabelled and nonterminal in each embedding,
so its number r_D of nonempty leaf regions should be2 or3. Source cores of
mass≤c^(1−r_D) then give three alternatives of mass≤1/c² each. Additive cut
cost follows because the two split source parents are distinct components.
The desired residual mass is≤3/c², with explicit actual-source-cut lifts.

If the overlap graph is a chain A—B—C with disjoint endpoint embeddings,
choose v in A∩B and w in B∩C. They are distinct. Four ownership assignments
give constraints B@v+C@w, B@{v,w}, A@v+C@w, A@v+B@w. For the middle-parent
double constraint, color by the nonempty leaf regions of T[B] minus {v,w},
using one r-color source core. Do not add the sizes of two overlapping
same-parent cut sets without proving their actual union cost.

When the middle has r≥3 nonempty regions, each of the four alternatives
has desired mass≤1/c², hence residual≤4/c² and full≤2/c+4/c^4. The latter
passes c=233/100 by Retarget233.lean.

**Coincident boundary case:** deleting two vertices can leave a leafless
middle region. If r=2, the two vertices may lie on one unbranched path of
T[B]. The required target statement is that every B-piece occupies v iff
it occupies w. If proved, the complete cover needs only two alternatives:
clear B at both vertices (one binary core), or clear A and C. Its desired
mass is≤1/c+1/c². This case must be checked rather than assigning an unpaid
second cut to B. r<2 should be ruled out from actual nonterminal span
geometry, not from a heuristic picture.

## Explicit graph and runtime debts

1. Actual minimal embeddings are connected/path-convex under the original
   unsuppressed address/graph representation; rooted restriction and history
   preserve the consuming geometry.
2. Triple-intersection vertex exists when the three parents pairwise
   intersect, with an explicit polynomial selector.
3. Each removal's nonempty leaf regions characterize exactly the avoiding
   leaf partitions, including leafless middle regions and root cases.
4. A valid final agreement partition occupies a fixed vertex through at
   most one parent; source-core refinement composes with that ownership.
5. The r-color generator has universal coverage, exact source cut witnesses,
   mass bound and budget-pruned generation cost; all graph lifts are proved.
6. The two-region chain coincidence assertion and reduced two-parent cases
   receive explicit rules and charged fallbacks.
7. Every remaining source rule/case, including isolated bad/good parents,
   is supplied at its exact hypothesis and with the sharper actual local
   budgets in SCAFFOLD-233-CASE-TARGET.md. If unavailable, its actual fallback
   cost stays in the exponent analysis.

Generation of a budget-pruned binary core can itself have many search nodes.
Any additive O*(2^q) generation bound is a theorem to prove and charge; the
strict2.33 recurrence slack could then absorb it, but it cannot be called
polynomial preprocessing. All intermediate state/cut/history objects and
original-label forest reconstruction belong in the production algorithm.

This candidate is a revised algorithm route with a named consuming state and
quantified payoff. It is not a standalone lemma request or a claimed proved
2.33 algorithm. Preserve the earlier edge-only2.31 rejections and the exact
enumerative fallback limitations.
