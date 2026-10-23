import Rule5QueryDomains
import ClassifierFeeBinding
import ClassifierFeePolynomial
import LiteralInterface
import Hard2RouteSource
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.FastOrdinary
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence

/-- Only checked agreement is consumed. Distinct optimal forest witnesses
are allowed; equality with another solver's chosen witness is not required. -/
def CallbackSound (cb : Ordinary) : Prop := ∀T S r F,DepthOne.proper T S=true→cb T S r=some F→agreement T S F=true

theorem cutoff_sound (q : Nat) : CallbackSound (cutoff solve q) := by
 intro T S r F hp hf
 by_cases below:r<q
 · have returned:solve r T S=some F:=by simpa only [cutoff,below,ite_true] using hf
   exact (query_sound (solve_exact r T S hp) returned).1
 · simp only [cutoff,below,ite_false] at hf

theorem common_sound_payloads (cb : Ordinary) (sound : CallbackSound cb) (d : Setup) (r : Nat) {FX FY FM FN : Forest}
 (fx:cb d.tx d.sx r=some FX) (fm:cb d.mxT d.mxS r=some FM) {p : RMAF.Vertex}
 (pre:DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy:FY=DepthOne.forest d.sy (some p)) (fn:outsideReply d FY=some FN) :
 Rule5LocalWork.cells FX≤2*(leaves d.T).length ∧ Rule5LocalWork.cells FY≤2*(leaves d.T).length ∧
 Rule5LocalWork.cells FM≤2*(leaves d.T).length ∧ Rule5LocalWork.cells FN≤2*(leaves d.T).length := by
 have op:=ordinary_pair_proper d
 have mp:=marked_pair_setup_proper d
 have xp:=Rule5LocalWork.agreement_payload d.tx d.sx FX (proper_left_nodup op) (sound _ _ _ _ op fx)
 have mf:=Rule5LocalWork.agreement_payload d.mxT d.mxS FM (proper_left_nodup mp) (sound _ _ _ _ mp fm)
 have xs:=Rule5ActualTrace.restricted_size d.nt d.htx
 have ms:=Rule5ActualTrace.marked_size d.nt d.hMXT
 have found:=found_one_minimum d.ty d.sy p pre
 have yp:=Rule5LocalWork.agreement_payload d.ty d.sy (DepthOne.forest d.sy (some p))
  (RestrictionBridge.restricted_nodup d.T d.ty d.Y d.hty d.nt) found.1
 have ys:=Rule5ActualTrace.restricted_size d.nt d.hty
 obtain ⟨F,out,aF,_,_⟩:=outsideReply_spec d _ found.1 found.2.1
 have out':outsideReply d FY=some F:=by rw [fy];exact out
 have eq:F=FN:=Option.some.inj (out'.symm.trans fn)
 have np:=Rule5LocalWork.agreement_payload d.myT d.myS F (proper_left_nodup (marked_outside_proper d)) aF
 have ns:=Rule5ActualTrace.marked_size d.nt d.hMYT
 subst F
 exact ⟨by omega,by rw [fy];omega,by omega,by omega⟩

theorem common_sound_reconstruct_work (cb : Ordinary) (sound : CallbackSound cb) (d : Setup) (r : Nat) {FX FY FM FN : Forest}
 (fx:cb d.tx d.sx r=some FX) (fm:cb d.mxT d.mxS r=some FM) {p : RMAF.Vertex}
 (pre:DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy:FY=DepthOne.forest d.sy (some p)) (fn:outsideReply d FY=some FN) :
 (Rule5LocalWork.reconstructMeter (measuredAgreement d.T d.S) d FX FY FM FN).work≤
 Rule5LocalWork.commonPolynomial (2*(leaves d.T).length) (agreementK (leaves d.T).length) := by
 have pay:=common_sound_payloads cb sound d r fx fm pre fy fn
 have blocks:=Rule5LocalWork.setup_blocks d
 have caps:=setup_tree_node_caps d
 apply Rule5LocalWork.reconstruct_polynomial (measuredAgreement d.T d.S) d FX FY FM FN
  (2*(leaves d.T).length) (agreementK (leaves d.T).length)
  (by omega) (by omega) pay.1 pay.2.1 pay.2.2.1 pay.2.2.2
 intro G hg
 have pG:=Rule5LocalWork.merge_payload d.X d.Y d.x d.y d.rho d.gamma FM FN
  (2*(leaves d.T).length) pay.2.2.1 pay.2.2.2 (by rw [Rule5LocalWork.merge_value];exact hg)
 exact measuredAgreement_K d.T d.S (leaves d.T).length caps.1 caps.2 G (by omega)
end Universal233.Rule5ClosedSource
