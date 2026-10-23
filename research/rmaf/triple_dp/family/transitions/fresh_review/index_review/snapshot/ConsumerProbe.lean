import IndexRoute

namespace TripleDP.FreshIndexReview
open CostRoute CostRoute.IndexRoute

/-- The consumer remains conditional on an actual parent family and both fields. -/
theorem conditional_consumer {α I J : Type} {l r : BTree α}
    [DecidableEq I] [DecidableEq J]
    (L : Family l I) (R : Family r J) (o : I) (p : J)
    (ho : L.boundary = some o) (hp : R.boundary = some p)
    (G : Family (.node l r) (Joined o p))
    (hfinite : G.finite = mergedFinite L.finite R.finite o p)
    (hboundary : G.boundary = some Joined.boundary) :
    G.cost = L.cost + R.cost ∧
      G.closedIndices = closedEnumeration L.finite.elems R.finite.elems o p := by
  have h := family_consumer_equations L R o p ho hp G hfinite hboundary
  exact ⟨h.2.2, h.2.1⟩

#print axioms conditional_consumer
#check @family_consumer_equations
#check @mergedFinite
end TripleDP.FreshIndexReview
