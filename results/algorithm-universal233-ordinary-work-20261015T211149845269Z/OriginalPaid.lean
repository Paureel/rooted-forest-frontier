import OriginalCaller

namespace Universal233.MafScheduler
open RMAF PaidQueries RestrictionBridge

theorem agreement_single_sameShape (t s : Tree) (B : List Nat)
    (ha : agreement t s [B]=true) : sameShape t s=true := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  have covers : ∀ L, partitionCheck L [B]=true → ∀ x∈L, x∈B := by
    intro L hp x hx
    obtain ⟨K,hK,hxK⟩ := checked_covers L [B] hp hx
    have he : K=B := by simpa using hK
    simpa [he] using hxK
  have ht : restrict B t=some t := restrict_of_contains t B
    (fun x hx => List.contains_iff_mem.2 (covers (leaves t) hh.1.1.1.1 x hx))
  have hs : restrict B s=some s := restrict_of_contains s B
    (fun x hx => List.contains_iff_mem.2 (covers (leaves s) hh.1.1.1.2 x hx))
  have hr := List.all_eq_true.1 hh.1.1.2 B (by simp)
  simpa [restrictionAgrees,ht,hs] using hr

theorem local_bad_minimum_positive (T S t s : Tree) (U : List Nat) (m : Nat)
    (ht : restrict U T=some t) (hs : restrict U S=some s)
    (hm : LocalMinimum t s m) (hbad : restrictionAgrees T S U=false) : 0<m := by
  by_cases hnot : 0<m
  · exact hnot
  have hz : m=0 := by omega
  obtain ⟨F,hF,hcost⟩ := hm.1
  have hne := DepthOne.agreement_nonempty t s F hF
  have hlen : F.length=1 := by have := List.length_pos_iff.2 hne; omega
  cases F with
  | nil => contradiction
  | cons B rest =>
    have he : rest=[] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hlen; omega)
    subst rest
    have hh := agreement_single_sameShape t s B hF
    simp [restrictionAgrees,ht,hs,hh] at hbad

def badParents (T S : Tree) (Q : Forest) : Nat :=
  (Q.map (fun U => if restrictionAgrees T S U then 0 else 1)).sum

theorem badSlots_minimum (m : P → Nat) (valid : P → A → Prop)
    (js : List (Job P A)) (hp : ∀ j∈js, Planned m valid j) :
    badSlots js= ((js.map Job.problem).map (fun U => if m U=0 then 0 else 1)).sum := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    have ht := ih (planned_tail m valid j js hp)
    have hh := hp j (by simp)
    cases j with
    | resolved p c a =>
      simp only [Planned] at hh
      simp [badSlots,Job.problem,hh.1,ht]
    | hard p =>
      have hz : m p≠0 := by simp only [Planned] at hh; omega
      simp [badSlots,Job.problem,hz,ht]

theorem actual_bad_count (T S : Tree) (Q : Forest) (t s : List Nat → Tree) (m : List Nat → Nat)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U))
    (hm : ∀ U∈Q, LocalMinimum (t U) (s U) (m U))
    (js : List (Job (List Nat) Forest)) (hkeys : js.map Job.problem=Q)
    (hp : ∀ j∈js, Planned m (LocalValid t s m) j) : badParents T S Q≤badSlots js := by
  rw [badSlots_minimum m (LocalValid t s m) js hp,hkeys]
  apply sum_map_le
  intro U hU
  cases hb : restrictionAgrees T S U with
  | true => simp [hb]
  | false =>
    have hz : m U≠0 := by
      have hmpos := local_bad_minimum_positive T S (t U) (s U) U (m U)
        (ht U hU) (hs U hU) (hm U hU) hb
      omega
    simp [hb,hz]

/-- A paid trace bound for the ACTUAL original-tree caller. The guard counts
    genuinely nonhomeomorphic original restricted components. Local exactness
    is still the future recursive IH; graph disjointness is retained by the
    correctness theorem, not inferred from this mass inequality. -/
theorem disjoint_actual_paid_mass (T S : Tree) (Q : Forest)
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (t s : List Nat → Tree) (m : List Nat → Nat)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U))
    (hm : ∀ U∈Q, LocalMinimum (t U) (s U) (m U))
    (solve : Tree → Tree → Nat → Option Forest) (q : Nat)
    (hbad : 2≤badParents T S Q) (c : Rat) (hc : 2≤c) :
    actualQueryMass c q (calls T S solve q Q)≤c^(-1 : Int) := by
  obtain ⟨js,hprep,hkeys,hplan⟩ := prepare_planned T S Q t s m ht hs
    (checked_block_proper T S Q pt ps hQT hQS t s ht hs) hm
  have hb := actual_bad_count T S Q t s m ht hs hm js hkeys hplan
  have hcals : calls T S solve q Q=(schedule (recursive T S solve) q js).calls := by
    simp [calls,attempt,hprep]
  rw [hcals]
  exact actual_paid_query_mass (recursive T S solve) q js (by omega) c hc
end Universal233.MafScheduler
