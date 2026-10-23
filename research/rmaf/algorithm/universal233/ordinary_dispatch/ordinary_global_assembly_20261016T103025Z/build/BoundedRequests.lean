import CurrentQuery
import PaidRequests
namespace Universal233.Rule5PaidOrdinary
open RMAF ForestState ForestMinCompletion
open Rule5Case322 Rule5FinalClassification Case322PaidGuard Rule5PaidSelector

abbrev BelowIH (q : Nat) (actual : Ordinary) : Prop := ∀ r,r<q → LocalOrdinaryIH r actual

theorem selected_paid_positive {T S : Tree} (R : SelectedPaid T S) (c : Branch)
 (hc : c∈guardedPlan R.geometry) : 0<c.originalCuts.length := by
 have hm : paid c∈(guardedPlan R.geometry).map paid := List.mem_map.2 ⟨c,hc,rfl⟩
 rcases guarded_cost_classes R.geometry with h | ⟨d,hd,h⟩
 · rw [h] at hm
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
   unfold paid at hm
   omega
 · rw [h] at hm
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
   unfold paid at hm
   omega

theorem request_decrease {T S : Tree} (R : SelectedPaid T S) {q : Nat} {Q : PaidRequest}
 (mem : Q∈requests R.geometry q) : Q.residual<q := by
 obtain ⟨c,hc,hQ⟩ := List.mem_filterMap.1 mem
 obtain ⟨aff,branch,target,sources,residual⟩ := requestFor_binding hQ
 have positive := selected_paid_positive R c hc
 unfold paid at aff
 rw [residual]
 change q-c.originalCuts.length<q
 omega

theorem request_payment_exact {T S : Tree} (R : SelectedPaid T S) {q : Nat} {Q : PaidRequest}
 (mem : Q∈requests R.geometry q) : Q.residual+Q.branch.originalCuts.length=q := by
 obtain ⟨c,hc,hQ⟩ := List.mem_filterMap.1 mem
 obtain ⟨aff,branch,target,sources,residual⟩ := requestFor_binding hQ
 rw [branch,residual]
 unfold paid at aff ⊢
 omega

theorem request_not_malformed (actual : Ordinary) {T S : Tree} {a b : Nat}
 {R : SelectedPaid T S} (built : buildSelected T S a b=some R) {q : Nat} {Q : PaidRequest}
 (mem : Q∈requests R.geometry q) :
 currentQuery actual (some Q.target) Q.sources Q.residual≠.malformed := by
 obtain ⟨c,hc,hQ⟩ := List.mem_filterMap.1 mem
 obtain ⟨aff,branch,target,sources,residual⟩ := requestFor_binding hQ
 have proper := full_state_proper R.geometry c (selected_actual_guards built c hc)
 intro malformed
 have bad := (currentQuery_malformed_iff actual (some Q.target) Q.sources Q.residual).1 malformed
 rw [target,sources] at bad
 simp [proper] at bad

def answers (actual : Ordinary) {T S : Tree} (R : SelectedPaid T S) (q : Nat) : List Forest :=
 (requests R.geometry q).filterMap (fun Q => currentAnswer actual (some Q.target) Q.sources Q.residual)

def originalAccepted (T S : Tree) (q : Nat) (F : Forest) : Bool :=
 agreement T S F && decide (F.length-1≤q)

theorem request_answer_sound (actual : Ordinary) {T S : Tree} {a b : Nat}
 {R : SelectedPaid T S} (built : buildSelected T S a b=some R) {q : Nat} {Q : PaidRequest}
 (mem : Q∈requests R.geometry q) {F : Forest}
 (answer : currentAnswer actual (some Q.target) Q.sources Q.residual=some F) :
 agreement T S F=true ∧ F.length-1≤q := by
 have hs := currentAnswer_sound actual (some Q.target) Q.sources Q.residual answer
 exact selected_full_request_sound built mem hs.1 hs.2

theorem answers_sound (actual : Ordinary) {T S : Tree} {a b : Nat}
 {R : SelectedPaid T S} (built : buildSelected T S a b=some R) {q : Nat} {F : Forest}
 (mem : F∈answers actual R q) : originalAccepted T S q F=true := by
 obtain ⟨Q,hQ,answer⟩ := List.mem_filterMap.1 mem
 have hs := request_answer_sound actual built hQ answer
 simpa [originalAccepted] using hs

/-- Only strict smaller-budget ordinary correctness is consumed, at each
actual request's full-list residual. No global ordinary IH is an input. -/
theorem answers_cover (actual : Ordinary) {T S : Tree} {a b : Nat}
 {R : SelectedPaid T S} (built : buildSelected T S a b=some R) (q : Nat)
 (below : BelowIH q actual) (G : Forest) (ha : agreement T S G=true) (budget : G.length-1≤q) :
 ∃ F,F∈answers actual R q ∧ originalAccepted T S q F=true ∧ F.length≤G.length := by
 obtain ⟨Q,hQ,proper,H,hH,len,cost,payment⟩ := selected_full_request_cover built q ha budget
 have ih := below Q.residual (request_decrease R hQ)
 obtain ⟨F,hF,least⟩ := currentAnswer_complete actual (some Q.target) Q.sources Q.residual ih H hH cost
 have hm : F∈answers actual R q := List.mem_filterMap.2 ⟨Q,hQ,hF⟩
 exact ⟨F,hm,answers_sound actual built hm,Nat.le_trans least len⟩
end Universal233.Rule5PaidOrdinary
