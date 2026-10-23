import PaidRequests
import CurrentQuery
import GroupCost
import SelectedExact
import PaidCallerBinding
import ControlFlowV4

/- One-shot independent consumer reconstruction. All support proof bodies unread. -/
open RMAF Universal233

namespace CleanRule5Verify20261022

def GuardedSurvival : Prop := ∀ (T S : Tree)
    (D : Case322PaidGuard.LiteralGeometry T S) (G : List (List Nat)),
    agreement T S G = true → ∃ c ∈ Case322PaidGuard.guardedPlan D,
      ∃ H, agreement T S H = true ∧ H.length ≤ G.length ∧
        VertexGeometry.Refines H c.partition

theorem refinement_length {T S : Tree} (c : Rule5Case322.Branch)
    (guard : Rule5Case322.currentGuard T S c = true)
    (H : List (List Nat)) (ha : agreement T S H = true)
    (href : VertexGeometry.Refines H c.partition) : c.partition.length ≤ H.length := by
  have hparts := BinaryExchange.agreement_parts T S H ha
  have hH : partitionCheck (leaves (Rule5Case322.current T S c)) H = true := by
    unfold Rule5Case322.current
    split
    · exact hparts.2.1
    · exact hparts.1
  have hQ := (Rule5PaidSelector.guard_current_parts guard).1
  have htotal := RestrictionBridge.total_family_length
    (leaves (Rule5Case322.current T S c)) H c.partition hH hQ href
  have positive : ∀ U ∈ c.partition, 0 < (RestrictionBridge.family U H).length := by
    intro U hU
    have ne := RestrictionBridge.family_nonempty
      (leaves (Rule5Case322.current T S c)) H c.partition hH hQ href U hU
    cases hh : RestrictionBridge.family U H with
    | nil => exact False.elim (ne hh)
    | cons a tail => simp only [List.length_cons]; omega
  have hsum := RestrictionBridge.sum_sub_one c.partition
    (fun U => (RestrictionBridge.family U H).length) positive
  omega

theorem paid_coverage (survival : GuardedSurvival)
    (actual : Rule5PaidOrdinary.Ordinary) {T S : Tree}
    (R : Rule5PaidSelector.SelectedPaid T S) (q : Nat)
    (smaller : ∀ r, r < q → ForestMinCompletion.LocalOrdinaryIH r actual)
    (G : List (List Nat)) (ha : agreement T S G = true) (budget : G.length - 1 ≤ q) :
    ∃ F, F ∈ Rule5PaidOrdinary.answers actual R q ∧
      Rule5PaidOrdinary.originalAccepted T S q F = true ∧ F.length ≤ G.length := by
  obtain ⟨c, hc, H, hH, hHG, href⟩ := survival T S R.geometry G ha
  have guard : Rule5Case322.currentGuard T S c = true := (List.mem_filter.mp hc).2
  have hcount := (Rule5PaidSelector.guard_current_parts guard).2.2
  have hlen := refinement_length c guard H hH href
  have affordable : Rule5Case322.paid c ≤ q := by omega
  have hHbudget : H.length - 1 ≤ q := by omega
  let Q : Rule5PaidSelector.PaidRequest :=
    { branch := c, target := Rule5PaidSelector.opposite T S c,
      sources := Rule5Case322.sourceForest T S c, residual := q - Rule5Case322.paid c }
  have hrequest : Rule5PaidSelector.requestFor T S q c = some Q := by
    simp only [Rule5PaidSelector.requestFor, affordable, ↓reduceIte]
    rfl
  have hQ : Q ∈ Rule5PaidSelector.requests R.geometry q := by
    exact List.mem_filterMap.mpr ⟨c, hc, hrequest⟩
  have hstate := (Rule5PaidSelector.full_state_paid_budget R.geometry c q guard affordable H).mpr
    ⟨hH, href, hHbudget⟩
  obtain ⟨F, hanswer, hFH⟩ := Rule5PaidOrdinary.currentAnswer_complete actual
    (some Q.target) Q.sources Q.residual (smaller Q.residual (Rule5PaidOrdinary.request_decrease R hQ))
    H hstate.1 hstate.2
  have hs := Rule5PaidOrdinary.currentAnswer_sound actual (some Q.target) Q.sources Q.residual hanswer
  have hresult := (Rule5PaidSelector.full_state_paid_budget R.geometry c q guard affordable F).mp hs
  refine ⟨F, ?_, ?_, Nat.le_trans hFH hHG⟩
  · exact List.mem_filterMap.mpr ⟨Q, hQ, hanswer⟩
  · simpa only [Rule5PaidOrdinary.originalAccepted, Bool.and_eq_true, decide_eq_true_eq] using
      And.intro hresult.1 hresult.2.2

theorem paid_best_exact (survival : GuardedSurvival)
    (actual : Rule5PaidOrdinary.Ordinary) {T S : Tree}
    (R : Rule5PaidSelector.SelectedPaid T S) (q : Nat)
    (smaller : ∀ r, r < q → ForestMinCompletion.LocalOrdinaryIH r actual) :
    Rule5OrdinaryDispatch.ExactAnswer T S q (Rule5PaidOrdinary.bestFor actual R q) := by
  constructor
  · intro F hbest
    have spec := RMAF.best_spec List.length (Rule5PaidOrdinary.originalAccepted T S q)
      (Rule5PaidOrdinary.answers actual R q) F hbest
    have hv : agreement T S F = true ∧ F.length - 1 ≤ q := by
      simpa only [Rule5PaidOrdinary.originalAccepted, Bool.and_eq_true, decide_eq_true_eq] using spec.2.1
    refine ⟨hv.1, hv.2, ?_⟩
    intro G hG
    by_cases hb : G.length - 1 ≤ q
    · obtain ⟨H, hm, hvH, hHG⟩ := paid_coverage survival actual R q smaller G hG hb
      exact Nat.le_trans (spec.2.2 H hm hvH) hHG
    · omega
  · intro G hG hb
    obtain ⟨H, hm, hvH, hHG⟩ := paid_coverage survival actual R q smaller G hG hb
    obtain ⟨F, hbest⟩ := RMAF.best_exists List.length (Rule5PaidOrdinary.originalAccepted T S q)
      (Rule5PaidOrdinary.answers actual R q) H hm hvH
    refine ⟨F, hbest, ?_⟩
    exact Nat.le_trans ((RMAF.best_spec List.length (Rule5PaidOrdinary.originalAccepted T S q)
      (Rule5PaidOrdinary.answers actual R q) F hbest).2.2 H hm hvH) hHG

#print axioms paid_best_exact

end CleanRule5Verify20261022
