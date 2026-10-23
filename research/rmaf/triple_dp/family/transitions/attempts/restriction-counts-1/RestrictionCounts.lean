import FamilyRestriction

namespace TripleDP.Transitions.Restriction
open TripleDP.CostRoute

variable {α I : Type} {l r : BTree α}

theorem filter_cover_count (xs : List I) (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q] (hc : ∀ i ∈ xs, P i ∨ Q i) :
    (xs.filter (fun i => decide (P i))).length +
      (xs.filter (fun i => decide (Q i))).length =
    xs.length + (xs.filter (fun i => decide (P i ∧ Q i))).length := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hh := hc i (by simp)
    have ht := ih (fun j hj => hc j (by simp [hj]))
    by_cases hp : P i <;> by_cases hq : Q i <;>
      simp [List.filter_cons, hp, hq] at hh ⊢ <;> omega

noncomputable def overlapIndices (A : Family (.node l r) I) : List I := by
  classical
  exact A.finite.elems.filter (fun i => decide (Live A false i ∧ Live A true i))

noncomputable def overlapCharge (A : Family (.node l r) I) : Nat := by
  classical
  exact if ∃ i, Live A false i ∧ Live A true i then 1 else 0

theorem overlap_count (A : Family (.node l r) I) :
    (overlapIndices A).length = overlapCharge A := by
  classical
  by_cases he : ∃ i, Live A false i ∧ Live A true i
  · rcases he with ⟨o, hl, hr⟩
    have hp (i : I) : (Live A false i ∧ Live A true i) ↔ i = o := by
      constructor
      · intro hi
        exact Option.some.inj ((both_live_boundary A i hi.1 hi.2).symm.trans
          (both_live_boundary A o hl hr))
      · rintro rfl; exact ⟨hl, hr⟩
    have hd := A.finite.nodup.count_of_mem (A.finite.complete o)
    simp only [overlapIndices, hp, List.filter_eq, List.length_replicate]
    simpa [overlapCharge, show ∃ i, Live A false i ∧ Live A true i from ⟨o, hl, hr⟩] using hd
  · have hp (i : I) : ¬ (Live A false i ∧ Live A true i) := fun hi => he ⟨i, hi⟩
    simp [overlapIndices, overlapCharge, he, hp]

theorem live_count_partition (A : Family (.node l r) I) :
    (liveIndices A false).length + (liveIndices A true).length =
      A.blockCount + overlapCharge A := by
  classical
  have h := filter_cover_count A.finite.elems (Live A false) (Live A true)
    (fun i _ => live_some_child A i)
  change (liveIndices A false).length + (liveIndices A true).length =
    A.blockCount + (overlapIndices A).length at h
  rw [overlap_count] at h
  exact h

theorem restrict_count_equation (A : Family (.node l r) I) (h : OpenBranchLive A) :
    (restrict A h false).blockCount + (restrict A h true).blockCount =
      A.blockCount + overlapCharge A := by
  rw [restrict_count, restrict_count]
  exact live_count_partition A

theorem restrict_cost_balance (A : Family (.node l r) I) (h : OpenBranchLive A) :
    A.cost + boundaryCharge A.boundary + overlapCharge A =
      (restrict A h false).cost + (restrict A h true).cost +
      boundaryCharge (restrict A h false).boundary +
      boundaryCharge (restrict A h true).boundary := by
  have hn := restrict_count_equation A h
  have hp := close_cost A
  have hl := close_cost (restrict A h false)
  have hr := close_cost (restrict A h true)
  omega

theorem overlap_iff_open (A : Family (.node l r) I) (o : I)
    (ho : A.boundary = some o) :
    (∃ i, Live A false i ∧ Live A true i) ↔ Live A false o ∧ Live A true o := by
  constructor
  · rintro ⟨i, hl, hr⟩
    have hi : i = o := Option.some.inj ((both_live_boundary A i hl hr).symm.trans ho)
    subst i
    exact ⟨hl, hr⟩
  · intro h; exact ⟨o, h⟩

theorem cost_closeBoth (A : Family (.node l r) I) (h : OpenBranchLive A)
    (ho : A.boundary = none) :
    A.cost = (restrict A h false).cost + (restrict A h true).cost +
      boundaryCharge (restrict A h false).boundary +
      boundaryCharge (restrict A h true).boundary := by
  have hn : ¬ ∃ i, Live A false i ∧ Live A true i := by
    rintro ⟨i, hl, hr⟩
    have hb := both_live_boundary A i hl hr
    simp [ho] at hb
  have hc := restrict_cost_balance A h
  simpa [overlapCharge, hn, ho, boundaryCharge] using hc

theorem cost_extendLeft (A : Family (.node l r) I) (h : OpenBranchLive A)
    (o : I) (ho : A.boundary = some o) (hl : Live A false o) (hr : ¬ Live A true o) :
    A.cost = (restrict A h false).cost + (restrict A h true).cost +
      boundaryCharge (restrict A h true).boundary := by
  have hn : ¬ ∃ i, Live A false i ∧ Live A true i := by
    intro hi; exact hr ((overlap_iff_open A o ho).mp hi).2
  have hb := restrict_open_boundary A h o ho false hl
  have hc := restrict_cost_balance A h
  simp only [overlapCharge, if_neg hn, ho, hb, boundaryCharge] at hc
  omega

theorem cost_extendRight (A : Family (.node l r) I) (h : OpenBranchLive A)
    (o : I) (ho : A.boundary = some o) (hl : ¬ Live A false o) (hr : Live A true o) :
    A.cost = (restrict A h false).cost + (restrict A h true).cost +
      boundaryCharge (restrict A h false).boundary := by
  have hn : ¬ ∃ i, Live A false i ∧ Live A true i := by
    intro hi; exact hl ((overlap_iff_open A o ho).mp hi).1
  have hb := restrict_open_boundary A h o ho true hr
  have hc := restrict_cost_balance A h
  simp only [overlapCharge, if_neg hn, ho, hb, boundaryCharge] at hc
  omega

theorem cost_merge (A : Family (.node l r) I) (h : OpenBranchLive A)
    (o : I) (ho : A.boundary = some o) (hl : Live A false o) (hr : Live A true o) :
    A.cost = (restrict A h false).cost + (restrict A h true).cost := by
  have hn : ∃ i, Live A false i ∧ Live A true i := ⟨o, hl, hr⟩
  have hbL := restrict_open_boundary A h o ho false hl
  have hbR := restrict_open_boundary A h o ho true hr
  have hc := restrict_cost_balance A h
  simp only [overlapCharge, if_pos hn, ho, hbL, hbR, boundaryCharge] at hc
  omega

#print axioms filter_cover_count
#print axioms overlap_count
#print axioms live_count_partition
#print axioms restrict_count_equation
#print axioms restrict_cost_balance
#print axioms overlap_iff_open
#print axioms cost_closeBoth
#print axioms cost_extendLeft
#print axioms cost_extendRight
#print axioms cost_merge
end TripleDP.Transitions.Restriction
