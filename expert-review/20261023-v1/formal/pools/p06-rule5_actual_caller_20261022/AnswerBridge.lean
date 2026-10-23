import QueryBridge
import SelectedExact

namespace ActualRule5Caller
open RMAF Universal233 ForestState ForestMinCompletion
open Universal233.Rule5Case322 Universal233.Rule5FinalClassification
open Universal233.Case322PaidGuard Universal233.Rule5PaidSelector
open Universal233.Rule5PaidOrdinary

theorem request_answer_sound_direct (actual : Ordinary) {T S : Tree}
    (D : LiteralGeometry T S) {q : Nat} {Q : PaidRequest}
    (member : Q ∈ requests D q) {F : Forest}
    (answer : currentAnswer actual (some Q.target) Q.sources Q.residual = some F) :
    agreement T S F = true ∧ F.length - 1 ≤ q := by
  obtain ⟨c,hc,hQ⟩ := List.mem_filterMap.mp member
  obtain ⟨aff,branch,target,sources,residual⟩ := requestFor_binding hQ
  have valid := currentAnswer_sound actual (some Q.target) Q.sources Q.residual answer
  rw [target,sources,residual] at valid
  have bound := (full_state_paid_budget D c q (List.mem_filter.mp hc).2 aff F).mp valid
  exact ⟨bound.1,bound.2.2⟩

theorem answers_cover_from_g0 (actual : Ordinary) {T S : Tree}
    (R : SelectedPaid T S) (q : Nat) (below : BelowIH q actual)
    (G : Forest) (hG : agreement T S G = true) (budget : G.length - 1 ≤ q) :
    ∃ F ∈ answers actual R q, originalAccepted T S q F = true ∧ F.length ≤ G.length := by
  obtain ⟨Q,hQ,H,hH,least,cost⟩ := requests_cover_from_g0 R.geometry q G hG budget
  have ih := below Q.residual (request_decrease R hQ)
  obtain ⟨F,hF,minimal⟩ := currentAnswer_complete actual (some Q.target) Q.sources Q.residual ih H hH cost
  have member : F ∈ answers actual R q := List.mem_filterMap.mpr ⟨Q,hQ,hF⟩
  have sound := request_answer_sound_direct actual R.geometry hQ hF
  refine ⟨F,member,?_,Nat.le_trans minimal least⟩
  simpa [originalAccepted] using sound

theorem best_sound_direct (actual : Ordinary) {T S : Tree}
    (R : SelectedPaid T S) (q : Nat) {F : Forest}
    (found : bestFor actual R q = some F) :
    agreement T S F = true ∧ F.length - 1 ≤ q := by
  have accepted := (best_spec List.length (originalAccepted T S q) (answers actual R q) F found).2.1
  simpa [originalAccepted] using accepted

theorem best_complete_from_g0 (actual : Ordinary) {T S : Tree}
    (R : SelectedPaid T S) (q : Nat) (below : BelowIH q actual)
    (G : Forest) (hG : agreement T S G = true) (budget : G.length - 1 ≤ q) :
    ∃ F, bestFor actual R q = some F ∧ F.length ≤ G.length := by
  obtain ⟨H,member,accepted,len⟩ := answers_cover_from_g0 actual R q below G hG budget
  obtain ⟨F,found⟩ := best_exists List.length (originalAccepted T S q) (answers actual R q) H member accepted
  have least := (best_spec List.length (originalAccepted T S q) (answers actual R q) F found).2.2 H member accepted
  exact ⟨F,found,Nat.le_trans least len⟩

theorem best_minimum_from_g0 (actual : Ordinary) {T S : Tree}
    (R : SelectedPaid T S) (q : Nat) (below : BelowIH q actual)
    {F : Forest} (found : bestFor actual R q = some F) :
    ∀ G, agreement T S G = true → F.length ≤ G.length := by
  have feasible := best_sound_direct actual R q found
  intro G hG
  by_cases bound : G.length - 1 ≤ q
  · obtain ⟨H,hH,least⟩ := best_complete_from_g0 actual R q below G hG bound
    have eq : H = F := Option.some.inj (hH.symm.trans found)
    simpa [eq] using least
  · omega

theorem selected_exact_from_g0 (actual : Ordinary) {T S : Tree} {a b : Nat}
    (R : SelectedPaid T S) (built : buildSelected T S a b = some R)
    (q : Nat) (below : BelowIH q actual) :
    (∀ F, solveSelected actual T S a b q = .answered (some F) →
      agreement T S F = true ∧ F.length - 1 ≤ q ∧
      ∀ G, agreement T S G = true → F.length ≤ G.length) ∧
    (∀ G, agreement T S G = true → G.length - 1 ≤ q →
      ∃ F, solveSelected actual T S a b q = .answered (some F) ∧ F.length ≤ G.length) := by
  constructor
  · intro F found
    have hb : bestFor actual R q = some F := by simpa [solveSelected,built] using found
    have sound := best_sound_direct actual R q hb
    exact ⟨sound.1,sound.2,best_minimum_from_g0 actual R q below hb⟩
  · intro G hG budget
    obtain ⟨F,hF,least⟩ := best_complete_from_g0 actual R q below G hG budget
    exact ⟨F,by simp [solveSelected,built,hF],least⟩

#print axioms selected_exact_from_g0
end ActualRule5Caller
