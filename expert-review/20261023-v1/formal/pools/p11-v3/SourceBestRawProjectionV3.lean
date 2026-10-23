import SchedulerRawProjectionV3

namespace SourceBestRawV3
open RMAF Universal233 WholeSourceWork OrdinaryDispatch.Hard2SourceWork

-- Own structural calculation from the licensed body; no saved sourceBest theorem.
theorem value {α : Type} (cost : α→Charged Nat) (valid : α→Charged Bool) (xs : List α) :
    (sourceBestMeter cost valid xs).value=
      best (fun x=>(cost x).value) (fun x=>(valid x).value) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [sourceBestMeter,best,ih]
    by_cases hc:(valid x).value=true
    · simp only [hc,Bool.false_eq_true,↓reduceIte]
      split <;> rename_i hr <;> simp only [hr]
      all_goals first | rfl | (split <;> rfl)
    · simp only [hc,Bool.false_eq_true,↓reduceIte]
end SourceBestRawV3
