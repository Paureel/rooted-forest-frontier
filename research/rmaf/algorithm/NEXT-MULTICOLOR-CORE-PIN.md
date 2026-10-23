# Post-delivery candidate: paid multi-color splitting core

Versioned theory-finding target after the topology-free2.31 chain rejection.
Not proved. Do not redirect an in-flight proof task; use this as a fresh
relaunch target after a new separate X0 and a frozen delivery checkpoint.

## Exact consuming algorithm and payoff

The four ownership assignments of an actual three-parent overlap chain need
two endpoint binary cores or a middle-parent simultaneous two-edge-clearing
core. The middle target partitions its source labels into three nonempty
target-side regions. A universal r-color source splitting-core mass bound
at c≥2 of c^(1−r), with coverage by label-partition refinement and paid
nonredundant source cuts, would give ≤1/c² for that middle branch. Combined
with the other assignments it would give residual mass≤4/c² and full
`2/c+4/c^4`, which is already kernel-checked below1 at c=233/100.
At a three-parent common edge there are only three survivor alternatives.
The unchanged published hard-case vector fails2.33, so both new cases and
all other scaffold/generation/correctness interfaces still must be supplied.

## Proposed production generator, to falsify before construction

Input: a rooted binary source tree with each distinct label assigned one of
r used colors. Return a source cut core covering every source-valid
monochromatic leaf partition by refinement; no target optimum query.

1. Coarsen/contract homogeneous cherries, recording their original labels
   and a proved cut-realization/refinement map. A color group may be a whole
   subtree, not merely an original leaf.
2. If only one color remains, emit no further cuts.
3. If a color occurs in only one current leaf group, detach that group by
   one counted source cut and recurse on the remaining labelled tree.
4. Otherwise pick a mixed cherry. Branch on detaching either pure-colored
   child group by one counted source cut, suppress the unary vertex and
   recurse. Each removed color still occurs elsewhere.
5. Deduplicate identical returned leaf partitions if useful; retain one
   actual source cut witness with its true cost and original-label lift.
   Prune children exceeding the actual remaining cut budget.

## Hypotheses to prove; none implicitly granted

- Homogeneous-cherry coarsening preserves coverage of EVERY source-valid
  monochromatic partition by refinement. It need not preserve the input
  partition exactly or target agreement of the intermediate coarsening.
- In a normalized mixed cherry, at least one pure child group can be
  detached in a core coarsened by the input partition.
- The unique-color detachment is forced at the partition-refinement level.
- Every emitted source partition is realizable by d=pieces−1 nonredundant
  cuts, including suppression/root cases; reconstruction is explicit.
- At base2 the proposed recursion has total core mass≤2^(1−r), and every
  emitted core has d≥r−1. Their composition yields c^(1−r) at c≥2.
- Generation is polynomial per counted search node/emitted child, with
  budget-pruned prefix work included. Minimum cut size alone is insufficient.

## Pre-registered plants for fresh X0

T=((0,1),(2,3)), colors0,2=A and1,3=B: the two extremal monochromatic
source partitions are [[0,2],[1],[3]] and[[0],[1,3],[2]], both two cuts.
Their unsplit pair/pair partition overlaps and is rejected. Any claim of a
single deterministic chosen core must expose the other partition as missed.
T=((0,1),2), colors0,1=A and2=B: one-cut core [[0,1],[2]], and the
three-singleton partition refines it.
T=((0,1),2), all three colors distinct: unique final monochromatic
partition is three singletons, two cuts.
T=((0,1),(2,3)), colors0,3=A,1=B,2=C: detaching the unique B and C leaves
an A pair and costs two; include root and unary suppression checks.
Deliberately omit a mixed-cherry branch on the crossed two-color quartet;
the nonempty clean twin must cover both extremal partitions.
Demand exact coverage of all source-valid monochromatic partitions on a
small frozen colored-tree census after measured pilots, not only optimum
colored partitions. Finite survival leaves every universal statement open.

## Formal and independent acceptance

Write total executable core and candidate integration only after X0. Prove
the actual graph/refinement statements in Lean with no sorry/admit/custom
unproved axioms/native_decide and retain complete axiom audits and false
proposition controls. Nonauthor fresh graph enumeration and every consumer
hypothesis/paid recurrence replay required before closure. Even a closed core
alone does not discharge the complete rMAF scaffold or prove a new algorithm.
