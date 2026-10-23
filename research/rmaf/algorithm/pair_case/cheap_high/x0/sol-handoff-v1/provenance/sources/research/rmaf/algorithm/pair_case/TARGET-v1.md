# Pair-case universal graph targets

Pinned 2026-10-15 after the completed conditional profile case, before new
dedicated universal graph proof construction. Main consumer:
`algorithm/scaffold_profiles/CASE-ARGUMENT-v2.md` (SHA-256
`730e843c456567fb42b5145c316613b01c6ec5803ef41465de739fa18925db7d`).
All three main algorithm milestones remain OPEN.

## G: actual mutually clear selector

Let T be an original rooted binary tree with distinct leaf labels, and let
A,B be disjoint nonempty subsets of its leaves. Let HA and HB be the actual
unsuppressed `RMAF.minimalVertices` embeddings, with nonempty intersection.
The occupied leaf regions at a shared vertex are connected components of
the original tree with that vertex removed which contain a selected leaf.

Prove an executable choice of either:

1. A shared original vertex at which A or B has three occupied leaf regions;
   or
2. An oriented original target edge e=(u,v) contained in both embeddings.
   Set D to the original descendant leaf labels below v, A1=A intersect D,
   A2=A minus D, B1=B intersect D, B2=B minus D. All four sets are nonempty.
   For each i, Hull(Ai) is disjoint from HB; for each j, Hull(Bj) is disjoint
   from HA. These are actual original-address embeddings.

The narrower equivalent consumer is: if every shared vertex has exactly two
occupied regions for both parents, construct choice 2. Supply the actual
minimalVertices/region-degree correspondence, not an assumed selector field.
Root, empty/singleton selections, absent/repeated labels and suppressed-path
traps must retain their precise applicability/refusal behavior.

## E: binary homeomorphic-parent exchange

Let S,T be original rooted binary trees on the same distinct leaf labels.
Let P be a proper source partition with disjoint actual source embeddings.
Choose distinct blocks A,B of P and an oriented original target edge e.
Its descendant leaf set D gives the four nonempty sectors above, satisfying
both mutual-clear predicates. Every other parent of P has target embedding
disjoint from HA and HB. Assume the restrictions S|A and T|A are rooted
homeomorphic. No homeomorphism of the whole parent B is assumed.

For EVERY agreement partition F of S,T refining P, construct an agreement
partition F' of S,T refining P such that:

- A is one whole block of F';
- every F' block inside B lies wholly in D or wholly outside D;
- the number of F' blocks is at most the number of F blocks;
- blocks outside A and B are unchanged.

Prove this for the actual executable rooted agreement/partition/embedding
definitions. The symmetry with B homeomorphic is allowed. An actual source
cut witness for the split inside an agreed final B block is a stronger useful
delivery, but must not be confused with cutting the WHOLE original B into
its two colors in one cut. Source-cost and reconstruction interfaces not
proved by a partition-level theorem must remain explicitly OPEN.

## MAY assume

- Original `lean/RMAF.lean` definitions and printed hypotheses.
- Independently reviewed frozen original-address geometry package and its
  actual minimalVertices-to-Hull theorem, at the exact stated hypotheses.
- Frozen local core graph/cherry lemmas at their stated premises.
- Elementary finite-tree path facts if proved or explicitly imported with
  retained source/axiom evidence.

## MUST NOT assume

The selector, mutual-clear conclusion, exchange, actual residual cut
components, universal source generation/coverage, original state history,
full running time, or a new faster algorithm. No field named as one of these
conclusions may replace its proof. No unrestricted-color or three-region
version of E is licensed. No ordinary/displayed edge is silently treated as
one original edge through suppression.

## Preregistered exact T1 and false controls

Use the literal seven-label pair:

    S = (((1,2),((3,5),(4,6))),7)
    T = (((1,(3,4)),(2,(5,6))),7)
    A = {1,2}, B = {3,4,5,6}, C = {7}.

The retained bounded referee calculation reports overlap vertices 0,00,01,
both overlap edges mutually clear, and optimum five components both without
and with A retained, in BOTH cases restricted to partitions refining
P={A,B,C}, among 877 enumerated partitions each. No unrestricted whole-input
optimum is supplied. Independently reconstruct these values.
The six-block agreement partition
{1}|{2}|{3,5}|{4}|{6}|{7} exchanges to
{1,2}|{3}|{5}|{4}|{6}|{7}. This is a local structural fixture, NOT an admitted
global hard-scaffold example. A root-promoted six-label target is a control
for the original root inside the shared path.

Before attacking the targets, freeze and run literal planted controls for
identical trees, wrong rooted topology, false forest validity/optimum, actual
suppressed paths, absent labels and boundary orientation. Catch the false
claim that original B above can be split into {3,4}|{5,6} by one source cut.
Catch an unqualified three-region exchange or report exactly which proposed
false plant was not actually false. Do not tune the control expectation to a
candidate output. Reuse of the adversary's own existing checker is permitted
and must be disclosed; importing the profile author/referee X0 code is not.

## Stages, alternatives, and acceptance

First a separate adversary runs a measured small original-graph pilot and
hostile cases without reading the candidate argument/proof. A finite no-fire
licenses universal proof construction but proves neither G nor E. A genuine
in-regime fire stops only the affected target, with exact witness, all guards
and values. Out-of-scope failures do not shift the target. A broken pin is
reported as a versioned erratum, never silently repaired during a proof.

Then use distinct original-address geometry and source/target agreement
surgery proof routes, with no unfinished cross-reading. Lean must reject
deliberately false statements and a compilable custom axiom; allow only the
standard propext/Classical.choice/Quot.sound axioms. Nonauthor source replay,
semantic checks and consuming-interface trace are required before scoped
acceptance. A successful target alone is not a complete algorithm or a
smaller-base theorem. All work, artifacts and hosting remain local.
