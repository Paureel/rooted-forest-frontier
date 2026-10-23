# Exact remaining source call after the two-guard stage

The actual admitted source is:
  let P := pendantPartition S a b
  properPair T S && hasCherry T a b && earlierClear T S && ...

The properPair and hasCherry Boolean body bills are now proved, including every
raw malformed/refused input and original cherry/address scan. The actual let P
construction is NOT covered by those guard bills. Under strict-let evaluation,
the first unresolved body is pendantPartition S a b -> cuts S a b ->
pendantOriginal S a b -> vertices S, then minimalVertices/rootedSpan/address
membership and source subtree-label/core construction. Source closure sharing
and compiled evaluation order have no claimed machine correspondence here.

The prefix rejection theorem is functional only: it does not make this earlier
P construction free. Later unresolved bodies include earlierClear/candidates
in both orientations, rule4 in both orientations, embeddings/restriction checks,
and the rest of selectLocal/selectBad/selectBoundary and selected builders.
No geometry obligation, desired SourceIH or global LocalWorkBound stands in for
these actual source-operation bills.

Full admitted / Rule5 classifier / builder / caller polynomial, complete bit
recurrence, improved base and main milestones remain OPEN. This is a concrete
source-body increment from the previous frozen first admitted guard gap.
