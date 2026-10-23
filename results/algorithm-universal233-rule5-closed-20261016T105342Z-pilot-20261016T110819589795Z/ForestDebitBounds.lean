import UniformPrefix
namespace Universal233.Rule5ClosedSource
open RMAF ForestState CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration
open WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5SelectedLocalWork Rule5PaidSelector Case322PaidGuard Rule5Case322
open ClassifierCheckFee PaidLiteralDecisionWork

def forestEnvelope (N Q q : Nat) : Rat :=geometric Rule5ActualTrace.base*(forestCoefficient N Q:Rat)*Rule5ActualTrace.base^q

theorem forest_envelope_nonneg (N Q q : Nat) : 0≤forestEnvelope N Q q := by
 unfold forestEnvelope
 exact Rat.mul_nonneg (Rat.mul_nonneg (geometric_properties _ (by decide +kernel)).2.2.1 Rat.natCast_nonneg)
  (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))

theorem current_debit_bound (cb : Ordinary) (T : Option Tree) (ss : List Tree) (r q N Q : Nat)
 (size:(labels T).length≤N) (budget:q≤Q) (rq:r≤q) (proper0:proper T ss=true) :
 ((currentQueryMeter cb (fun _ _ _=>0) T ss r).forestDebit:Rat)≤forestEnvelope N Q q := by
 have positive:=Rat.mul_nonneg (geometric_properties Rule5ActualTrace.base (by decide +kernel)).2.2.1 (show 0≤forestCoefficient N Q by unfold forestCoefficient;exact Rat.natCast_nonneg)
 have b:=forestLocalWork_bound cb T N Q Rule5ActualTrace.base (by decide +kernel) size ss r (by omega) proper0
 have pow:=Universal233.PaidQueries.qpow_mono Rule5ActualTrace.base (by decide +kernel) rq
 have scale:=Rat.mul_le_mul_of_nonneg_left pow positive
 simp only [currentQueryMeter]
 split
 · exact forest_envelope_nonneg N Q q
 · exact forest_envelope_nonneg N Q q
 · split
   · exact forest_envelope_nonneg N Q q
   · exact Rat.le_trans b scale

theorem answer_list_debit_sum (cb : Ordinary) (js : List PaidRequest) :
 (answerListMeter cb (fun _ _ _=>0) js).forestDebit=
 (js.map (fun j=>(currentQueryMeter cb (fun _ _ _=>0) (some j.target) j.sources j.residual).forestDebit)).sum := by
 induction js <;> simp_all [answerListMeter,requestAnswerMeter]

theorem answers_debit_bound (cb : Ordinary) {T S : Tree} (R : SelectedPaid T S) (q N Q : Nat)
 (tn:(leaves T).length≤N) (sn:(leaves S).length≤N) (budget:q≤Q) :
 ((answersMeter cb (fun _ _ _=>0) R q).forestDebit:Rat)≤4*forestEnvelope N Q q := by
 let js:=(requestsMeter R.geometry q).value
 have positive:=forest_envelope_nonneg N Q q
 have point (j:PaidRequest) (mem:j∈js) :
 ((currentQueryMeter cb (fun _ _ _=>0) (some j.target) j.sources j.residual).forestDebit:Rat)≤forestEnvelope N Q q := by
  have native:j∈requests R.geometry q:=by simpa only [requests_value,js] using mem
  obtain ⟨c,hc,hj⟩:=List.mem_filterMap.1 native
  obtain ⟨aff,branch,target,sources,residual⟩:=requestFor_binding hj
  have proper0:=full_state_proper R.geometry c (List.mem_filter.1 hc).2
  have size:(labels (some j.target)).length≤N:=by
   rw [target];change (leaves (opposite T S c)).length≤N
   unfold opposite;split <;> assumption
  exact current_debit_bound cb (some j.target) j.sources j.residual q N Q size budget
   (by rw [residual];omega) (by simpa only [target,sources] using proper0)
 have sum:=GenericForest.rat_sum_map_le js
  (fun j=>((currentQueryMeter cb (fun _ _ _=>0) (some j.target) j.sources j.residual).forestDebit:Rat))
  (fun _=>forestEnvelope N Q q) point
 rw [rat_sum_constant] at sum
 have count:js.length≤4:=requests_count R.geometry q
 have scale:=Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.2 count) positive
 simpa only [answersMeter,answer_list_debit_sum,nat_sum_cast,Rat.natCast_ofNat,js] using Rat.le_trans sum scale

theorem selected_forest_debit_bound (cb : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch:CherryAt T i a b) (ad:admitted T S a b=true) (q N Q : Nat) {z : FinalSelection}
 (sel:(finalMeter checkFee T S a b).value=some z)
 (tn:(leaves T).length≤N) (sn:(leaves S).length≤N) (budget:q≤Q) :
 (selectedForestDebit cb checkFee (literalFee T S a b) T S a b q z:Rat)≤5*forestEnvelope N Q q := by
 have positive:=forest_envelope_nonneg N Q q
 have forestCase (z:FinalSelection) (sel:(finalMeter checkFee T S a b).value=some z) :
 (childForestDebit cb (fun _ _ _=>0) T q (selectedChildrenMeter S a b z).value:Rat)≤5*forestEnvelope N Q q := by
  have properPair0:=properPair_parts (admitted_parts ad).1
  have hp (c:CherryBranching.Child) (mem:c∈(selectedChildrenMeter S a b z).value) : proper (some T) c.sourceForest=true := by
   have facts:=(Rule5OrdinaryDispatch.selected_forest_facts ch ad (by rw [←final_value checkFee];exact sel) (by simpa only [selected_children_value] using mem)).1
   rw [facts.2.2.2.1]
   exact OutputState.sourceForest_proper T S c.partition properPair0.1 properPair0.2.1 properPair0.2.2 facts.1
  simpa only [forestEnvelope,Rat.natCast_ofNat,Rat.mul_assoc] using childForestDebit_local_bound cb T q _ N Q 5 tn budget (selected_children_count S a b z) hp
 cases z with
 | «prefix» s=>exact forestCase _ sel
 | remaining d z=>cases z with
  | first u v=>exact forestCase _ sel
  | third u v=>exact forestCase _ sel
  | one e=>exact Rat.mul_nonneg (by decide +kernel) positive
  | second u v=>
   simp only [selectedForestDebit,solveSelectedMeter]
   split
   · exact Rat.mul_nonneg (by decide +kernel) positive
   · rename_i R hr
     have b:=answers_debit_bound cb R q N Q tn sn budget
     have scale:4*forestEnvelope N Q q≤5*forestEnvelope N Q q:=Rat.mul_le_mul_of_nonneg_right (by decide +kernel) positive
     exact Rat.le_trans b scale
end Universal233.Rule5ClosedSource
