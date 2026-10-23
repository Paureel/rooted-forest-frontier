import OWRecovery
namespace OrdinaryDispatch.OptimizerLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.BudgetOptimization

/-- One selected recovery, one retained record; forest/certificate payloads are
references. No final recovery is evaluated on a completely failed scan. -/
def meterFinish (S : Tree) (r : Scan) : Charged Execution :=
 match r.selected with
 | none=>⟨⟨r,none,[]⟩,8⟩
 | some (_,F)=>let a:=meterRecovery S F;⟨⟨r,a.value,[(F,a.value)]⟩,a.work+12⟩
@[simp] theorem meterFinish_value (S : Tree) (r : Scan) : (meterFinish S r).value=finish S r := by
 cases h:r.selected with
 | none=>simp [meterFinish,finish,h]
 | some p=>obtain ⟨q,F⟩:=p;simp [meterFinish,finish,h]

theorem meterFinish_bound (S : Tree) (r : Scan) :
 (meterFinish S r).work≤12+
 ((finish S r).recoveries.map (fun call=>(FinalCutRecovery.meterRecover S call.1).work)).sum := by
 cases h:r.selected with
 | none=>simp [meterFinish,finish,h]
 | some p=>
  obtain ⟨q,F⟩:=p
  have a:=meterRecovery_le_legacy S F
  simp only [meterFinish,finish,h,Charged.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

/-- The only external bill is solve's explicit per-budget callback work w.
This definition does not prove that w bounds the actual solve implementation. -/
def meterOptimize (w : Nat→Nat) (T S : Tree) : Charged Execution :=
 let p:=meterPreflight T S
 if p.value.1 then
  let s:=meterScan (fun b=>⟨FastOrdinary.solve b T S,w b⟩) 0 p.value.2
  let f:=meterFinish S s.value
  ⟨f.value,p.work+s.work+f.work+8⟩
 else ⟨⟨⟨none,[]⟩,none,[]⟩,p.work+8⟩
@[simp] theorem meterOptimize_value (w T S) : (meterOptimize w T S).value=optimize T S := by
 simp only [meterOptimize,meterPreflight_value,meterFinish_value,meterScan_value,optimize]
 split <;> rfl

/-- Derived THREE fees: preflight=256*(N+1)^2, perTrial=12, finalRecord=32.
The statement covers arbitrary malformed refusal as well as every visited trial.
Recovery's legacy counter is included only at its actual selected call site. -/
theorem actual_wrapper_fees (w : Nat→Nat) (T S : Tree) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterOptimize w T S).work≤totalCharge w (preflightFee N) 12 32 S (optimize T S) := by
 have p:=meterPreflight_bound T S N tn sn
 by_cases hp:DepthOne.proper T S=true
 · let sc:=meterScan (fun b=>⟨FastOrdinary.solve b T S,w b⟩) 0 (leaves T).length
   have sv : sc.value=scan (fun b=>FastOrdinary.solve b T S) 0 (leaves T).length:=by
    simp only [sc,meterScan_value]
   have sw:=meterScan_accounting (fun b=>⟨FastOrdinary.solve b T S,w b⟩) 0 (leaves T).length
   change sc.work=trialWork w sc.value.trials+sc.administration at sw
   have sa: sc.administration≤12*sc.value.trials.length+2:=
    (meterScan_administration _ _ _).1
   have f:=meterFinish_bound S sc.value
   have result : optimize T S=finish S sc.value:=by simp only [optimize,hp,ite_true,sv]
   simp only [meterOptimize,meterPreflight_value,hp,ite_true]
   rw [result]
   simp only [totalCharge,wrapperCharge,finish_search]
   change (meterPreflight T S).work+sc.work+(meterFinish S sc.value).work+8≤_
   omega
 · have hf:DepthOne.proper T S=false:=Bool.eq_false_iff.2 hp
   simp [meterOptimize,meterPreflight_value,hf,optimize,totalCharge,wrapperCharge,trialWork]
   omega

/-- Polynomial envelope for the three derived fees, in raw original node count.
No current-state q<=leaf-count premise enters this local theorem. -/
theorem wrapper_polynomial (w : Nat→Nat) (T S : Tree) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 wrapperCharge (preflightFee N) 12 32 (optimize T S)≤512*(N+1)^2 := by
 have sc:=meterScan_administration
  (fun b=>⟨FastOrdinary.solve b T S,w b⟩) 0 (leaves T).length
 have n:=Nat.le_trans (leaves_nodes T) tn
 have p1 : N+1≤(N+1)^2:=by simpa using pow_mono N 1 2 (by decide)
 have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 by_cases hp:DepthOne.proper T S=true
 · have len : (optimize T S).search.trials.length≤N:=by
    simpa only [optimize,hp,ite_true,finish_search,meterScan_value] using Nat.le_trans sc.2 n
   simp only [wrapperCharge,preflightFee];omega
 · have hf:DepthOne.proper T S=false:=Bool.eq_false_iff.2 hp
   simp [wrapperCharge,optimize,hf,preflightFee];omega

/-- Reuses the frozen conditional exponential theorem with all three wrapper
fees now instantiated. It remains a counter theorem: actual solve work, scalar
interpretation and the old recovery generator source provider are external. -/
theorem conditional_233_derived_wrapper (T S : Tree) (hp : DepthOne.proper T S=true)
 (w : Nat→Nat) (N L A d : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N)
 (perQuery : ∀b,b<(leaves T).length →
   (w b:Rat)≤(queryPolynomial (leaves T).length b L A d:Rat)*(233/100:Rat)^b) :
 ∃o,(optimize T S).output=some o ∧ 0<o.partition.length ∧
 o.sourceCuts.length+1=o.partition.length ∧
 ((meterOptimize w T S).work:Rat)≤
 (((leaves T).length*uniformQueryPolynomial (leaves T).length L A d+
   (preflightFee N+12*(leaves T).length+32)+recoveryEnvelope (leaves T).length:Nat):Rat)*
   (233/100:Rat)^(o.partition.length-1) := by
 obtain ⟨o,out,pos,cost,bound⟩:=conditional_233 T S hp w (preflightFee N) 12 32 L A d perQuery
 exact ⟨o,out,pos,cost,Rat.le_trans (Rat.natCast_le_natCast.2 (actual_wrapper_fees w T S N tn sn)) bound⟩
end OrdinaryDispatch.OptimizerLocalWork
