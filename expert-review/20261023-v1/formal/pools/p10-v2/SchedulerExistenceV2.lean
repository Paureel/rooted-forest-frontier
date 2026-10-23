import CoupledSchedulerV2

namespace SourceCouplingV2
open Universal233.PaidQueries

variable {P A : Type} {Child : P → Nat → Option (Nat × A) → Prop}
  {mode : Mode} {b k ticks : Nat} {js : List (Job P A)}
  {r : MeterReceipt P A} {slots : List (Slot P A)}

theorem run_exists (total : ∀ p b, ∃ a, Child p b a)
    (mode : Mode) (b k : Nat) (js : List (Job P A)) :
    ∃ r slots ticks, Run Child mode b k js r slots ticks := by
  induction js generalizing k with
  | nil => exact ⟨_,_,_,Run.nil⟩
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      obtain ⟨r,slots,ticks,hr⟩ := ih k
      exact ⟨_,_,_,Run.resolved hr⟩
    | hard p =>
      cases hm : enabled mode b with
      | false => exact ⟨_,_,_,Run.refused hm⟩
      | true =>
        obtain ⟨a,ha⟩ := total p b
        cases a with
        | none => exact ⟨_,_,_,Run.failed hm ha⟩
        | some x =>
          obtain ⟨r,slots,ticks,hr⟩ := ih (k+1)
          exact ⟨_,_,_,Run.success hm ha hr⟩

theorem slot_lower (h : Run Child mode b k js r slots ticks)
    (s : Slot P A) (hs : s ∈ slots) : k ≤ s.index := by
  induction h with
  | nil => simp at hs
  | resolved tail ih => exact ih hs
  | refused off => simp only [List.mem_singleton] at hs; subst s; exact Nat.le_refl _
  | failed on returned => simp only [List.mem_singleton] at hs; subst s; exact Nat.le_refl _
  | success on returned tail ih =>
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact Nat.le_refl _
    · have z := ih hs
      omega

theorem run_slots_strict (h : Run Child mode b k js r slots ticks) :
    slots.Pairwise (fun s t => s.index < t.index) := by
  induction h with
  | nil => simp
  | resolved tail ih => exact ih
  | refused off => simp
  | failed on returned => simp
  | success on returned tail ih =>
    simp only [List.pairwise_cons]
    exact ⟨fun s hs => by have z := slot_lower tail s hs; omega, ih⟩

theorem run_live_slots_strict (h : Run Child mode b k js r slots ticks) :
    (liveSlots slots).Pairwise (fun s t => s.index < t.index) := by
  exact (run_slots_strict h).sublist (live_order slots)

theorem run_nth (h : Run Child mode b k js r slots ticks) (j : Nat) :
    (slots.map (fun s => (s.index,s.query)))[j]? =
      (r.queries[j]?).map (fun p => (k+j,p)) := by
  rw [run_slot_index h]
  exact CallbackPairingAuthor.indexFrom_nth k r.queries j

end SourceCouplingV2
