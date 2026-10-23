import MergeContract

namespace TripleDP.FreshMergeReview
open CostRoute Transitions

/-- A downstream consumer can extract actual indexing and root semantics, and
recover the merged label union from the existential support contract alone.
No decidable-equality hypothesis and no unfolding of the merge constructor. -/
theorem exported_interface_consumable {α I J : Type} {l r : BTree α}
    (f : Family l I) (g : Family r J) (o : I) (p : J)
    (ho : f.boundary = some o) (hp : g.boundary = some p) :
    ∃ A : Family (.node l r) (MergeIndex I p),
      A.finite.elems.Nodup ∧ (∀ k, k ∈ A.finite.elems) ∧
      (∀ k, A.support k [] ↔ A.boundary = some k) ∧
      (∀ x, A.hasLabel (.inl o) x ↔ f.hasLabel o x ∨ g.hasLabel p x) ∧
      A.blockCount = f.blockCount + g.blockCount - 1 ∧ A.cost = f.cost + g.cost := by
  rcases merge_universal f g o p ho hp with ⟨A, _, _, _, hm, hc, hk⟩
  refine ⟨A, A.finite.nodup, A.finite.complete, A.root_spec, ?_, hc, hk⟩
  intro x
  constructor
  · rintro ⟨a, hx, ha⟩
    rw [hm] at ha
    cases a with
    | nil => exact False.elim hx
    | cons side a =>
      cases side with
      | false => exact Or.inl ⟨a, hx, by simpa [liftSupport] using ha⟩
      | true => exact Or.inr ⟨a, hx, by simpa [liftSupport] using ha⟩
  · rintro (⟨a, hx, ha⟩ | ⟨a, hx, ha⟩)
    · refine ⟨false :: a, hx, ?_⟩
      rw [hm]
      exact Or.inr (Or.inl ⟨rfl, ha⟩)
    · refine ⟨true :: a, hx, ?_⟩
      rw [hm]
      exact Or.inr (Or.inr ⟨rfl, ha⟩)

#print axioms exported_interface_consumable
#check @merge
#check @merge_universal
end TripleDP.FreshMergeReview
