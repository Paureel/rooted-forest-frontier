import FamilyTrim

namespace TripleDP.Family.FreshReview

/-- Two charged indices cannot denote the same leaf-vertex block. -/
theorem closed_leafsets_injective (F : RawFamily t k) (i j : Fin k)
    (h : LeafSet t (F.closed i) = LeafSet t (F.closed j)) : i = j := by
  rcases F.closed_live i with ⟨v, hv⟩
  have hj : LeafSet t (F.closed j) v := h ▸ hv
  exact F.closed_disjoint i j v hv.2 hj.2

/-- The open leaf-vertex block cannot equal any charged leaf-vertex block. -/
theorem open_leafset_ne_closed (F : RawFamily t k) (R : Support)
    (hR : F.openRegion = some R) (i : Fin k) :
    LeafSet t R ≠ LeafSet t (F.closed i) := by
  intro heq
  rcases F.closed_live i with ⟨v, hv⟩
  have ho : LeafSet t R v := heq.symm ▸ hv
  exact F.open_disjoint R hR i v ho.2 hv.2

/-- The empty raw open is absent after normalization; the charge stays k. -/
theorem empty_open_normalizes_without_charge (F : RawFamily t k) (R : Support)
    (hR : F.openRegion = some R) (hempty : ¬ HasLeaf t R) :
    (normalize F).openRegion = none ∧ closedCost (normalize F) = k := by
  constructor
  · change trimOpen t F.openRegion = none
    rw [hR]
    exact trimOpen_empty t R hempty
  · rfl

#print axioms closed_leafsets_injective
#print axioms open_leafset_ne_closed
#print axioms empty_open_normalizes_without_charge
end TripleDP.Family.FreshReview
