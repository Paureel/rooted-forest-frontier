import ForestWorkBound
namespace GenericForest
open RMAF ForestState
open Universal233 Universal233.PaidQueries

theorem meter_run_query_keys {P A : Type} (rec : P → Nat → Option (Nat × A))
    (charge : P → Nat → Nat) (b : Nat) (js : List (Job P A)) :
    ∀ p k, (p,k) ∈ (meterRun rec charge b js).queries →
      k = b ∧ ∃ j ∈ js, j.problem = p := by
  induction js with
  | nil => simp [meterRun]
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      intro r k hk
      have hh := ih r k hk
      obtain ⟨j,hj,he⟩ := hh.2
      exact ⟨hh.1,j,by simp [hj],he⟩
    | hard p =>
      cases he : rec p b with
      | none =>
        intro r k hk
        have h : (r,k) = (p,b) := by simpa [meterRun,he] using hk
        cases h
        exact ⟨rfl,.hard p,by simp,rfl⟩
      | some x =>
        intro r k hk
        have hm : (r,k) = (p,b) ∨ (r,k) ∈ (meterRun rec charge b js).queries := by
          simpa [meterRun,he] using hk
        rcases hm with hh | ht
        · cases hh
          exact ⟨rfl,.hard p,by simp,rfl⟩
        · obtain ⟨hb,j,hj,hjp⟩ := ih r k ht
          exact ⟨hb,j,by simp [hj],hjp⟩

theorem actual_paid_query_smaller (ordinary : Tree → Tree → Nat → Option Forest)
    (ordinaryWork : Tree → Tree → Nat → Nat) (t : Tree) (ss : List Tree)
    (hp : proper (some t) ss = true) (hmultiple : 2 ≤ ss.length)
    (q : Nat) (js : List (Job (Tree × Tree) Forest)) (hj : jobs t ss = some js)
    (p : Tree × Tree) (k : Nat)
    (hk : (p,k) ∈ (meterSchedule
      (fun p b => (ordinary p.1 p.2 b).map (fun F => (F.length-1,F)))
      (fun p b => ordinaryWork p.1 p.2 b) q js).queries) :
    k ≤ q ∧ DepthOne.proper p.1 p.2 = true ∧
      (leaves p.1).length < (leaves t).length ∧ (leaves p.2).length < (leaves t).length := by
  unfold meterSchedule at hk
  split at hk
  · simp at hk
  · obtain ⟨he,j,hjj,hjp⟩ := meter_run_query_keys _ _ _ js p k hk
    have hb : k ≤ q := by simp only [allocated] at he; omega
    have hh := jobs_proper_and_smaller t ss hp hmultiple js hj j hjj
    exact ⟨hb,by simpa [hjp] using hh⟩

theorem duplicate_bills {α : Type} (L : List α) (f : α → Rat) :
    ((L++L).map f).sum = (L.map f).sum+(L.map f).sum := by
  simp only [List.map_append,List.sum_append]

private theorem actual_private_origin : 2+3=5 := by decide
theorem exported_private_origin : 2+3=5 := actual_private_origin

end GenericForest
