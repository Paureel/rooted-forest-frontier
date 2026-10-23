-- Own success soundness from actual final checks; no completeness theorem reused.
import BestMinimum13
import LocalExact
open RMAF ForestState
namespace HighCompletion
theorem best_success_valid {α : Type} (cost : α→Nat) (valid : α→Bool) {xs : List α} {F : α}
    (h : best cost valid xs=some F) : valid F=true := by
  have hb:=best_minimum cost valid xs
  rw [h] at hb
  exact hb.2.1
theorem forest_checked_sound (T : Option Tree) (ss : List Tree) (q : Nat)
    (G F : List (List Nat)) (h : GenericForest.checked T ss q G=some F) :
    agrees T ss F=true ∧ additionalCost ss F≤q := by
  unfold GenericForest.checked at h
  split at h
  next hv =>
    have he:=Option.some.inj h
    subst F
    simpa only [GenericForest.accepted,Bool.and_eq_true,decide_eq_true_eq] using hv
  next => cases h
theorem forest_disjoint_sound (actual : Tree→Tree→Nat→Option (List (List Nat)))
    (T : Tree) (ss : List Tree) (q : Nat) (F : List (List Nat))
    (h : GenericForest.disjointSolve T ss actual q=some F) :
    agrees (some T) ss F=true ∧ additionalCost ss F≤q := by
  unfold GenericForest.disjointSolve at h
  obtain ⟨r,_,hrest⟩:=Option.bind_eq_some_iff.mp h
  obtain ⟨xs,_,hc⟩:=Option.bind_eq_some_iff.mp hrest
  exact forest_checked_sound _ _ _ _ _ hc
theorem forest_solve_sound (actual : Tree→Tree→Nat→Option (List (List Nat)))
    (T : Option Tree) (ss : List Tree) (q : Nat) (F : List (List Nat))
    (h : GenericForest.solve actual T ss q=some F) :
    agrees T ss F=true ∧ additionalCost ss F≤q := by
  rw [GenericForest.solve.eq_def] at h
  split at h
  next hp =>
    split at h
    next hag =>
      have he:=Option.some.inj h
      subst F
      exact ⟨hag,by simp only [additionalCost,List.length_map,Nat.sub_self,Nat.zero_le]⟩
    next hn =>
      split at h
      next => cases h
      next t s =>
        obtain ⟨G,_,hc⟩:=Option.bind_eq_some_iff.mp h
        exact forest_checked_sound _ _ _ _ _ hc
      next t hnotSingle =>
        split at h
        next ho => exact forest_disjoint_sound actual t ss q F h
        next overlap hover =>
          dsimp only at h
          have hv:=best_success_valid List.length (GenericForest.accepted (some t) ss q) h
          simpa only [GenericForest.accepted,Bool.and_eq_true,decide_eq_true_eq] using hv
  next => cases h
#print axioms forest_solve_sound
end HighCompletion
