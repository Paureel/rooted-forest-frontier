import ControlFlowV4

/- One-shot independently authored conditional reconstruction. No premise inhabitant
   is used, and no candidate whole-solver theorem body was read or invoked. -/
open RMAF Universal233 OrdinaryDispatch
open OrdinaryDispatch.FastOrdinary IndependentReconstruction

namespace CleanGlobalVerify20261022

theorem conditional_query
    (ready : IndependentReconstruction.CommonReady)
    (lift : IndependentReconstruction.CommonLift)
    (one : IndependentReconstruction.OneRule)
    (high : IndependentReconstruction.HighRule)
    (forward4 : IndependentReconstruction.ForwardRule4)
    (reverse4 : IndependentReconstruction.ReverseRule4)
    (hard : IndependentReconstruction.Hard2Rule)
    (nonrefusal : IndependentReconstruction.RejectImpossible) :
    ∀ (q : Nat) (T S : Tree), DepthOne.proper T S = true →
      QueryExact T S q (FastOrdinary.solve q T S) := by
  intro q T S
  induction q, T, S using FastOrdinary.solve.induct with
  | case1 q T S hp hpre =>
      intro _
      unfold DepthOne.pretest01 at hpre
      rw [ite_eq_left hp] at hpre
      split at hpre <;> contradiction
  | case2 q T S hp c hpre _ =>
      intro _
      exact IndependentReconstruction.actual_solve_successful_pretest q hp hpre
  | case3 q T S hp c hpre _ =>
      intro _
      exact IndependentReconstruction.actual_solve_successful_pretest q hp hpre
  | case4 q T S hp hpre reverse c hearly p hn _ ihcommon =>
      intro _
      have hproper := (ready T S reverse c hp hpre hearly).1
      have hleaves := (ready T S reverse c hp hpre hearly).2
      have hexact := lift q T S reverse c
        (FastOrdinary.solve q (commonPair T S reverse c).1 (commonPair T S reverse c).2)
        hp hpre hearly (ihcommon hproper)
      rw [FastOrdinary.solve.eq_def]
      simpa only [hp, ↓reduceIte, hpre, hearly, hleaves, ↓reduceDIte] using hexact
  | case5 q T S hp hpre reverse c hearly p hn _ =>
      intro _
      exact False.elim (hn (ready T S reverse c hp hpre hearly).2)
  | case6 q T S hp hpre reverse c hearly ihpaid =>
      intro _
      have below : IndependentReconstruction.BelowBudget q := by
        intro r hr u v huv
        exact ihpaid u v r hr huv
      have hexact := one q T S reverse c hp hpre hearly below
      rw [FastOrdinary.solve.eq_def]
      simp only [hp, ↓reduceIte, hpre, hearly]
      exact hexact
  | case7 q T S hp hpre reverse c hearly ihpaid =>
      intro _
      have below : IndependentReconstruction.BelowBudget q := by
        intro r hr u v huv
        exact ihpaid u v r hr huv
      have hexact := high q T S reverse c hp hpre hearly below
      rw [FastOrdinary.solve.eq_def]
      simp only [hp, ↓reduceIte, hpre, hearly]
      exact hexact
  | case8 q T S hp hpre s hearly ihpaid =>
      intro _
      have below : IndependentReconstruction.BelowBudget q := by
        intro r hr u v huv
        exact ihpaid u v r hr huv
      have hexact := forward4 q T S s hp hpre hearly below
      rw [FastOrdinary.solve.eq_def]
      simp only [hp, ↓reduceIte, hpre, hearly]
      exact hexact
  | case9 q T S hp hpre s hearly ihpaid =>
      intro _
      have below : IndependentReconstruction.BelowBudget q := by
        intro r hr u v huv
        exact ihpaid u v r hr huv
      have hexact := reverse4 q T S s hp hpre hearly below
      rw [FastOrdinary.solve.eq_def]
      simp only [hp, ↓reduceIte, hpre, hearly]
      exact hexact
  | case10 q T S hp hpre c d hearly ihpaid =>
      intro _
      have below : IndependentReconstruction.BelowBudget q := by
        intro r hr u v huv
        exact ihpaid u v r hr huv
      have hexact := hard q T S c d hp hpre hearly below
      rw [FastOrdinary.solve.eq_def]
      simp only [hp, ↓reduceIte, hpre, hearly]
      exact hexact
  | case11 q T S hp hpre hearly _ =>
      intro _
      exact False.elim (nonrefusal T S hp hpre hearly)
  | case12 q T S hbad =>
      intro hp
      exact False.elim (hbad hp)

#check conditional_query
#print axioms conditional_query

end CleanGlobalVerify20261022
