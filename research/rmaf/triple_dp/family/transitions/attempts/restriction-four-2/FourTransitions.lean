import RecoverSplits
import RecoverMerge

namespace TripleDP.Transitions.Restriction
open TripleDP.CostRoute

variable {α I J : Type} {l r : BTree α}

def ExactRecovery {t : BTree α} (G : Family t J) (A : Family t I) (f : J → I) : Prop :=
  Represents G A f ∧ G.blockCount = A.blockCount ∧ G.cost = A.cost

theorem exact_recovery {t : BTree α} (G : Family t J) (A : Family t I)
    (f : J → I) (hf : Represents G A f) : ExactRecovery G A f :=
  ⟨hf, represents_count G A f hf, represents_cost G A f hf⟩

theorem represents_normal (G : Family (.node l r) J) (A : Family (.node l r) I)
    (f : J → I) (hf : Represents G A f) (hg : OpenBranchLive G) : OpenBranchLive A := by
  intro o ho side hh
  rcases hf.2.1 o with ⟨j, hj⟩
  have he : G.support j = A.support o := by rw [hf.2.2.1 j, hj]
  have hroot : G.support j [] := by rw [he]; exact (A.root_spec o).mpr ho
  have hocc : ∃ a, G.support j (side :: a) := by rw [he]; exact hh
  rcases hg j ((G.root_spec j).mp hroot) side hocc with ⟨a, x, hx, ha⟩
  exact ⟨a, x, hx, by rw [← he]; exact ha⟩

theorem four_transition_recovery (A : Family (.node l r) I) (h : OpenBranchLive A) :
    (∃ _ : A.boundary = none,
      ExactRecovery (closeBoth (restrict A h false) (restrict A h true)) A (splitMap A)) ∨
    (∃ (o : I) (ho : A.boundary = some o) (hl : Live A false o),
      ¬ Live A true o ∧
      ExactRecovery (extendLeft (restrict A h false) (restrict A h true) ⟨o, hl⟩
        (restrict_open_boundary A h o ho false hl)) A (splitMap A)) ∨
    (∃ (o : I) (ho : A.boundary = some o) (hr : Live A true o),
      ¬ Live A false o ∧
      ExactRecovery (extendRight (restrict A h false) (restrict A h true) ⟨o, hr⟩
        (restrict_open_boundary A h o ho true hr)) A (splitMap A)) ∨
    (∃ (o : I) (ho : A.boundary = some o) (hl : Live A false o) (hr : Live A true o),
      ExactRecovery (rejoin A h o ho hl hr) A (mergeMap A o hr)) := by
  classical
  have hb : A.boundary = none ∨ ∃ o, A.boundary = some o := by
    cases ho : A.boundary with
    | none => exact Or.inl rfl
    | some o => exact Or.inr ⟨o, rfl⟩
  rcases hb with ho | ⟨o, ho⟩
  · exact Or.inl ⟨ho, exact_recovery _ _ _ (recover_closeBoth A h ho)⟩
  ·
    by_cases hl : Live A false o
    · by_cases hr : Live A true o
      · exact Or.inr (Or.inr (Or.inr
          ⟨o, ho, hl, hr, exact_recovery _ _ _ (recover_merge A h o ho hl hr)⟩))
      · exact Or.inr (Or.inl
          ⟨o, ho, hl, hr, exact_recovery _ _ _ (recover_extendLeft A h o ho hl hr)⟩)
    · have hr : Live A true o := (live_some_child A o).resolve_left hl
      exact Or.inr (Or.inr (Or.inl
        ⟨o, ho, hr, hl, exact_recovery _ _ _ (recover_extendRight A h o ho hl hr)⟩))

#print axioms exact_recovery
#print axioms represents_normal
#print axioms four_transition_recovery
end TripleDP.Transitions.Restriction
