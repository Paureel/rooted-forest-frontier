import PaidForestCandidates
namespace Universal233.Rule5ExecutionSource
open RMAF ForestState CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence

/-- Unlike the ordinary pretest's constant cutCost, additionalCost traverses
both the candidate and current source list at each score occurrence. -/
def bestAdditionalMeter (ss : List Tree) (valid : Forest→Charged Bool) : List Forest→Charged (Option Forest)
 | []=>⟨none,1⟩
 | F::fs=>let a:=valid F;let r:=bestAdditionalMeter ss valid fs
           if a.value then
            match r.value with
            | none=>⟨some F,a.work+r.work+6⟩
            | some G=>⟨if ForestState.additionalCost ss F≤ForestState.additionalCost ss G then some F else some G,
               a.work+r.work+F.length+G.length+2*ss.length+8⟩
           else ⟨r.value,a.work+r.work+4⟩

theorem best_additional_value (ss : List Tree) (valid : Forest→Charged Bool) (fs : List Forest) :
 (bestAdditionalMeter ss valid fs).value=best (ForestState.additionalCost ss) (fun F=>(valid F).value) fs := by
 induction fs with
 | nil=>rfl
 | cons F fs ih=>
  simp only [bestAdditionalMeter,best]
  by_cases hv:(valid F).value=true
  · simp only [hv,ite_true]
    cases hr:(bestAdditionalMeter ss valid fs).value with
    | none=>rw [←ih,hr]
    | some G=>rw [←ih,hr]
  · simp only [hv,ite_false];exact ih

theorem best_additional_work (ss : List Tree) (valid : Forest→Charged Bool) (fs : List Forest) (K B : Nat)
 (checks : ∀F,F∈fs→(valid F).work≤K) (payload : ∀F,F∈fs→F.length≤B) :
 (bestAdditionalMeter ss valid fs).work≤(K+2*B+2*ss.length+10)*fs.length+1 := by
 induction fs with
 | nil=>simp [bestAdditionalMeter]
 | cons F fs ih=>
  have a:=checks F (by simp);have p:=payload F (by simp)
  have r:=ih (fun G hG=>checks G (by simp [hG])) (fun G hG=>payload G (by simp [hG]))
  simp only [bestAdditionalMeter]
  split
  · split
    · dsimp only;simp only [List.length_cons,Nat.mul_succ];omega
    · rename_i G hg
      have hbest : best (ForestState.additionalCost ss) (fun F=>(valid F).value) fs=some G := by rw [←best_additional_value];exact hg
      have gp:=payload G (by simp [(best_spec _ _ _ _ hbest).1])
      dsimp only;simp only [List.length_cons,Nat.mul_succ];omega
  · dsimp only;simp only [List.length_cons,Nat.mul_succ];omega

def forestPretestMeter (T : Option Tree) (ss : List Tree) : Charged ForestPretest01.Result :=
 let p:=meterProper T ss
 if p.value then
  let c:=forestCandidatesMeter ss;let b:=bestAdditionalMeter ss (meterAgrees T ss) c.value
  ⟨match b.value with | none=>.rejected | some F=>.found F,p.work+c.work+b.work+4⟩
 else ⟨.refused,p.work+2⟩

theorem forest_pretest_value (T : Option Tree) (ss : List Tree) :
 (forestPretestMeter T ss).value=ForestPretest01.pretest01 T ss := by
 simp only [forestPretestMeter,meterProper_value,forest_candidates_value,best_additional_value,meterAgrees_value,ForestPretest01.pretest01]
 split <;> simp_all <;> rfl
end Universal233.Rule5ExecutionSource
