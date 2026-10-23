/- Literal best semantics, including duplicate candidates and failed checks. -/
import ActualCommonLiftV5
open RMAF
namespace IndependentPaid

def PickSpec {α : Type} (cost : α→Nat) (valid : α→Bool) (xs : List α) : Option α→Prop
 | none=>∀x∈xs,valid x=false
 | some y=>y∈xs ∧ valid y=true ∧ ∀x∈xs,valid x=true→cost y≤cost x

theorem pick_spec {α : Type} (cost : α→Nat) (valid : α→Bool) (xs : List α) :
 PickSpec cost valid xs (best cost valid xs) := by
 induction xs with
 | nil => simp [best,PickSpec]
 | cons a rest ih =>
  cases va : valid a with
  | false =>
   simp only [best,va,Bool.false_eq_true,ite_false]
   cases ht : best cost valid rest with
   | none =>
    rw [ht] at ih
    try simp only [ht]
    intro x hx
    rcases List.mem_cons.1 hx with rfl|hx
    · exact va
    · exact ih x hx
   | some b =>
    rw [ht] at ih
    try simp only [ht]
    refine ⟨by simp [ih.1],ih.2.1,?_⟩
    intro x hx vx
    rcases List.mem_cons.1 hx with rfl|hx
    · simp [va] at vx
    · exact ih.2.2 x hx vx
  | true =>
   simp only [best,va,ite_true]
   cases ht : best cost valid rest with
   | none =>
    rw [ht] at ih
    try simp only [ht]
    refine ⟨by simp,va,?_⟩
    intro x hx vx
    rcases List.mem_cons.1 hx with rfl|hx
    · exact Nat.le_refl _
    · have impossible := ih x hx;rw [vx] at impossible;contradiction
   | some b =>
    rw [ht] at ih
    try simp only [ht]
    split
    · rename_i ab
      refine ⟨by simp,va,?_⟩
      intro x hx vx
      rcases List.mem_cons.1 hx with rfl|hx
      · exact Nat.le_refl _
      · exact Nat.le_trans ab (ih.2.2 x hx vx)
    · rename_i ab
      refine ⟨by simp [ih.1],ih.2.1,?_⟩
      intro x hx vx
      rcases List.mem_cons.1 hx with rfl|hx
      · omega
      · exact ih.2.2 x hx vx

theorem best_return {α : Type} (cost : α→Nat) (valid : α→Bool) (xs : List α)
 {y : α} (h : best cost valid xs=some y) :
 y∈xs ∧ valid y=true ∧ ∀x∈xs,valid x=true→cost y≤cost x := by
 have spec := pick_spec cost valid xs
 rw [h] at spec
 exact spec

theorem best_none {α : Type} (cost : α→Nat) (valid : α→Bool) (xs : List α)
 (h : best cost valid xs=none) : ∀x∈xs,valid x=false := by
 have spec := pick_spec cost valid xs
 rw [h] at spec
 exact spec

theorem best_witness {α : Type} (cost : α→Nat) (valid : α→Bool) (xs : List α)
 {x : α} (hx : x∈xs) (vx : valid x=true) :
 ∃y,best cost valid xs=some y ∧ cost y≤cost x := by
 cases h : best cost valid xs with
 | none => have no := best_none cost valid xs h x hx;rw [vx] at no;contradiction
 | some y => exact ⟨y,rfl,(best_return cost valid xs h).2.2 x hx vx⟩
end IndependentPaid
