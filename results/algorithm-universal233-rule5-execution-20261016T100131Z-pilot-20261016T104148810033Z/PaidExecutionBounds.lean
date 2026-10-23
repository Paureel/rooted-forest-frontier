import PaidBestSource
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence GenericForest.FrontierWork
open CherryBranching Rule5Case322 Rule5PaidSelector Case322PaidGuard Rule5SelectedLocalWork Rule5RemainingLocalWork Rule5PendantLocalWork

theorem request_state_caps {T S : Tree} (D : LiteralGeometry T S) (q N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) {j : PaidRequest} (mem:j∈requests D q) :
 targetNodes (some j.target)≤N ∧ sourceNodes j.sources≤2*N ∧ proper (some j.target) j.sources=true := by
 obtain ⟨c,hc,hj⟩:=List.mem_filterMap.1 mem
 obtain ⟨aff,branch,target,sources,residual⟩:=requestFor_binding hj
 have guard:currentGuard T S c=true:=(List.mem_filter.1 hc).2
 have caps:=current_tree_caps D c N tn sn
 have checks:=guard_current_parts guard
 have mat:=OutputState.checked_materialization (current T S c) c.partition caps.2 checks.1
 have perm:=FinalCutRecovery.checked_flatten_perm (current T S c) c.partition caps.2 checks.1
 have plen : ((Rule5Case322.sourceForest T S c).map leaves).flatten.length=(leaves (current T S c)).length :=
  mat.2.1.length_eq.trans perm.length_eq
 have nodes:=forest_nodes_le_leaves (Rule5Case322.sourceForest T S c)
 have ln:=Nat.le_trans (leaves_nodes (current T S c)) caps.1
 have source : sourceNodes j.sources≤2*N:=by
  rw [sources];unfold sourceNodes;omega
 have targ : targetNodes (some j.target)≤N:=by
  rw [target];unfold targetNodes opposite
  split <;> assumption
 have hp:=full_state_proper D c guard
 exact ⟨targ,source,by simpa only [target,sources] using hp⟩

theorem answer_list_prefix_rows (cb : Ordinary) (W : OrdinaryWork) (js : List PaidRequest) (N : Nat)
 (states : ∀j,j∈js→targetNodes (some j.target)≤N ∧ sourceNodes j.sources≤N) :
 (answerListMeter cb W js).prefixWork≤(currentPrefixBudget N+4)*js.length+1 := by
 induction js with
 | nil=>simp [answerListMeter]
 | cons j js ih=>
  have st:=states j (by simp)
  have a:=current_prefix_work cb W (some j.target) j.sources j.residual N st.1 st.2
  have r:=ih (fun k hk=>states k (by simp [hk]))
  simp only [answerListMeter,requestAnswerMeter,List.length_cons,Nat.mul_succ];omega

def answersPrefixBudget (T S : Tree) (N : Nat) :=requestsBudget T S N+4*(currentPrefixBudget (2*N)+4)+3

theorem answers_prefix_work (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (answersMeter cb W R q).prefixWork≤answersPrefixBudget T S N := by
 have req:=requests_work R.geometry q N tn sn
 have cnt:=requests_count R.geometry q
 have rows:=answer_list_prefix_rows cb W (requestsMeter R.geometry q).value (2*N) (by
  intro j hj
  have h:=request_state_caps R.geometry q N tn sn (by simpa only [requests_value] using hj)
  exact ⟨by omega,h.2.1⟩)
 have scale:=Nat.mul_le_mul_left (currentPrefixBudget (2*N)+4) cnt
 simp only [answersMeter,answersPrefixBudget];omega

theorem answers_payload (cb : Ordinary) {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (built:buildSelected T S a b=some R) (q : Nat) {F : Forest} (mem:F∈Rule5PaidOrdinary.answers cb R q) :
 F.flatten.length=(leaves T).length ∧ F.length≤(leaves T).length := by
 have valid:=Rule5PaidOrdinary.answers_sound cb built mem
 have parts : agreement T S F=true ∧ decide (F.length-1≤q)=true:=by simpa only [Rule5PaidOrdinary.originalAccepted,Bool.and_eq_true] using valid
 have ha:agreement T S F=true:=parts.1
 have part:partitionCheck (leaves T) F=true:=(BinaryExchange.agreement_parts T S F ha).1
 exact ⟨(FinalCutRecovery.checked_flatten_perm T F R.geometry.properT part).length_eq,SourceCoverage.partitionCheck_block_bound _ _ part⟩

def paidBestBudget (T S : Tree) (N n : Nat) :=answersPrefixBudget T S N+4*(agreementK n+3*n+7)+7

theorem best_for_prefix_work (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (built:buildSelected T S a b=some R) (q N n : Nat) (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (tnn:treeNodes T≤2*n) (snn:treeNodes S≤2*n) (ln:(leaves T).length≤n) :
 (bestForMeter cb W R q).prefixWork≤paidBestBudget T S N n := by
 have pref:=answers_prefix_work cb W R q N tn sn
 have count:(answersMeter cb W R q).value.length≤4:=by
  rw [answers_value,Rule5PaidOrdinary.answers]
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simpa only [requests_value] using requests_count R.geometry q)
 have payload (F) (hf:F∈(answersMeter cb W R q).value) : F.flatten.length≤n ∧ F.length≤n:=by
  have p:=answers_payload cb built q (by simpa only [answers_value] using hf);omega
 have best:=best_length_work (originalAcceptedMeter T S q) (answersMeter cb W R q).value (agreementK n+n+3) n (by
  intro F hf
  have p:=payload F hf
  have k:=measuredAgreement_K T S n tnn snn F (by unfold Rule5LocalWork.cells;omega)
  simp only [originalAcceptedMeter];omega) (fun F hf=>(payload F hf).2)
 have scale:=Nat.mul_le_mul_left (agreementK n+n+3+2*n+4) count
 simp only [bestForMeter,paidBestBudget]
 have coef:agreementK n+n+3+2*n+4=agreementK n+3*n+7:=by omega
 rw [coef] at best scale
 omega
end Universal233.Rule5ExecutionSource
