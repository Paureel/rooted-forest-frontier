import CommonPaidSource
import CommonPolynomial
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence

/-- Output length is bounded before the final budget comparison, including
unstable concatenation and the stable literal owner-pair search. -/
theorem reconstruct_length (d : Setup) (FX FY FM FN : Forest) (N : Nat)
 (fx : Rule5LocalWork.cells FX≤N) (fy : Rule5LocalWork.cells FY≤N)
 (fm : Rule5LocalWork.cells FM≤N) (fn : Rule5LocalWork.cells FN≤N)
 {G : Forest} (answer : reconstruct d FX FY FM FN=some G) : G.length≤2*N+1 := by
 unfold reconstruct at answer
 split at answer
 · unfold pickMerge at answer
   have mem:=(best_spec _ _ _ _ answer).1
   have bound:=Rule5LocalWork.merge_payload d.X d.Y d.x d.y d.rho d.gamma FM FN N fm fn (by rw [Rule5LocalWork.merge_value];exact mem)
   exact bound.2
 · cases Option.some.inj answer
   unfold Rule5LocalWork.cells at fx fy
   simp only [List.length_append];omega

theorem common_actual_payloads (d : Setup) (r : Nat) {FX FY FM FN : Forest}
 (fx : Rule5LocalWork.actual d.tx d.sx r=some FX)
 (fm : Rule5LocalWork.actual d.mxT d.mxS r=some FM) {p : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy : FY=DepthOne.forest d.sy (some p)) (fn : outsideReply d FY=some FN) :
 Rule5LocalWork.cells FX≤2*(leaves d.T).length ∧ Rule5LocalWork.cells FY≤2*(leaves d.T).length ∧
 Rule5LocalWork.cells FM≤2*(leaves d.T).length ∧ Rule5LocalWork.cells FN≤2*(leaves d.T).length := by
 have mn:=Rule5LocalWork.common_real_payload d r fm pre fy fn
 have xp:=Rule5LocalWork.closed_payload d.tx d.sx r (ordinary_pair_proper d) fx
 have xs:=Rule5ActualTrace.restricted_size d.nt d.htx
 have yp:=found_one_minimum d.ty d.sy p pre
 have yf:=Rule5LocalWork.agreement_payload d.ty d.sy (DepthOne.forest d.sy (some p))
  (RestrictionBridge.restricted_nodup d.T d.ty d.Y d.hty d.nt) yp.1
 have ys:=Rule5ActualTrace.restricted_size d.nt d.hty
 exact ⟨by omega,by rw [fy];omega,mn.1,mn.2⟩

/-- Reuse the completed general agreement bridge at the actual common
reconstruction consumer. No primitive agreement-fee hypothesis remains. -/
theorem common_reconstruct_work (d : Setup) (r : Nat) {FX FY FM FN : Forest}
 (fx : Rule5LocalWork.actual d.tx d.sx r=some FX)
 (fm : Rule5LocalWork.actual d.mxT d.mxS r=some FM) {p : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy : FY=DepthOne.forest d.sy (some p)) (fn : outsideReply d FY=some FN) :
 (Rule5LocalWork.reconstructMeter (measuredAgreement d.T d.S) d FX FY FM FN).work≤
 Rule5LocalWork.commonPolynomial (2*(leaves d.T).length) (agreementK (leaves d.T).length) := by
 have caps:=setup_tree_node_caps d
 exact Rule5LocalWork.actual_common_reconstruct_polynomial d r fx fm pre fy fn
  (measuredAgreement d.T d.S) (agreementK (leaves d.T).length)
  (fun G hg=>measuredAgreement_K d.T d.S (leaves d.T).length caps.1 caps.2 G hg)

def paidBudget (n : Nat) :=Rule5LocalWork.commonPolynomial (2*n) (agreementK n)+4*n+30

theorem run_paid_local (W : OrdinaryWork) (d : Setup) (q : Nat) {FY FN : Forest} {p : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy : FY=DepthOne.forest d.sy (some p)) (fn : outsideReply d FY=some FN) :
 (runPaidMeter Rule5LocalWork.actual W d q FY FN).localWork≤paidBudget (leaves d.T).length := by
 by_cases zero:q=0
 · subst q
   simp only [runPaidMeter,paidJobsMeter,if_pos rfl,jobsAnswersMeter]
   unfold paidBudget;dsimp only;omega
 · have js : (paidJobsMeter d q).value=[⟨d.tx,d.sx,q-1⟩,⟨d.mxT,d.mxS,q-1⟩] := by simp [paidJobsMeter,zero]
   have jw : (paidJobsMeter d q).work=12 := by simp [paidJobsMeter,zero]
   cases fx:Rule5LocalWork.actual d.tx d.sx (q-1) with
   | none=>simp only [runPaidMeter,js,jw,jobsAnswersMeter,fx];unfold paidBudget;dsimp only;omega
   | some FX=>
    cases fm:Rule5LocalWork.actual d.mxT d.mxS (q-1) with
    | none=>simp only [runPaidMeter,js,jw,jobsAnswersMeter,fx,fm];unfold paidBudget;dsimp only;omega
    | some FM=>
     have rec:=common_reconstruct_work d (q-1) fx fm pre fy fn
     have pay:=common_actual_payloads d (q-1) fx fm pre fy fn
     simp only [runPaidMeter,js,jw,jobsAnswersMeter,fx,fm]
     split
     · unfold paidBudget;dsimp only;omega
     · rename_i G hg
       have len:=reconstruct_length d FX FY FM FN (2*(leaves d.T).length) pay.1 pay.2.1 pay.2.2.1 pay.2.2.2
        (by rw [←reconstruct_actual_agreement];exact hg)
       unfold paidBudget;dsimp only;omega
end Universal233.Rule5ExecutionSource
