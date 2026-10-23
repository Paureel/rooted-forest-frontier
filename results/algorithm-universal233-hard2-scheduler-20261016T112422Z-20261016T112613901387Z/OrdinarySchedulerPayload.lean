import OrdinarySchedulerWeighted
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.BothBad Universal233.PaidQueries
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork

theorem flatten_answer_caps (xs : List (Nat×List (List Nat))) (N : Nat)
 (caps:∀x,x∈xs→x.2.length≤N ∧ x.2.flatten.length≤2*N) :
 (xs.flatMap Prod.snd).length≤N*xs.length ∧
 (xs.flatMap Prod.snd).flatten.length≤(2*N)*xs.length:=by
 induction xs with
 | nil=>simp
 | cons x xs ih=>
   have head:=caps x (by simp)
   have tail:=ih (by intro y hm;exact caps y (by simp [hm]))
   simp only [List.flatMap_cons,List.length_append,List.flatten_append,List.length_cons,Nat.mul_add,Nat.mul_one]
   exact ⟨by omega,by omega⟩

theorem ordinaryLocalSource_payload (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (parts : List (List Nat)) (b N : Nat) (three:3≤N)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (F : List (List Nat)) (h:(ordinaryLocalSource actual T S parts b).value.answer=some F) :
 F.length≤N*parts.length ∧ F.flatten.length≤(2*N)*parts.length:=by
 simp only [ordinaryLocalSource,ordinaryPrepareMeter_value] at h
 cases prep:MafScheduler.prepare T S parts with
 | none=>simp only [prep] at h;cases h
 | some js=>
   simp only [prep,optionFlattenMeter_value] at h
   cases ans:(scheduleSourceMeter (mafRecursiveMeter actual T S) b js).value.answers with
   | none=>simp only [ans,Option.map_none] at h;cases h
   | some xs=>
     have eq:(xs.flatMap Prod.snd)=F:=by simpa only [ans,Option.map_some,Option.some.injEq] using h
     subst F
     have caps:=scheduleSourceMeter_answer_payload (mafRecursiveMeter actual T S) b js
      (fun F=>F.length≤N ∧ F.flatten.length≤2*N)
      (by intro U c F hm;have p:=prepared_resolved_payload T S parts N sn js prep U c F hm;exact ⟨by omega,p.2⟩)
      (by intro U hm x ha;have p:=mafRecursiveMeter_payload actual T S U _ N tn x ha;exact ⟨p.1,by omega⟩) xs ans
     have result:=flatten_answer_caps xs N caps.2
     rw [caps.1,prepare_length T S parts js prep] at result
     exact result

def ordinaryCheckSize (N L : Nat):=N*(L+1)+N
theorem ordinary_checked_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (parts : List (List Nat)) (b q N : Nat) (three:3≤N)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) :
 (checkedMeter T S q (ordinaryExecution (GenericForest.solve actual) T S parts b).answer).work≤
 agreementK (ordinaryCheckSize N parts.length)+N*parts.length+6:=by
 cases answer:(ordinaryExecution (GenericForest.solve actual) T S parts b).answer with
 | none=>simp only [checkedMeter];omega
 | some F=>
   have source:(ordinaryLocalSource actual T S parts b).value.answer=some F:=by
     simpa only [ordinaryLocalSource_value] using answer
   have payload:=ordinaryLocalSource_payload actual T S parts b N three tn sn F source
   simp only [Nat.mul_assoc] at payload
   have check:=measuredAgreement_K T S (ordinaryCheckSize N parts.length)
    (by simp only [ordinaryCheckSize,Nat.mul_add,Nat.mul_one];omega)
    (by simp only [ordinaryCheckSize,Nat.mul_add,Nat.mul_one];omega) F
    (by simp only [Rule5LocalWork.cells,ordinaryCheckSize,Nat.mul_add,Nat.mul_one,Nat.mul_assoc];omega)
   change (agreementMeter T S F).work≤agreementK (ordinaryCheckSize N parts.length) at check
   simp only [checkedMeter]
   omega
end OrdinaryDispatch.Hard2SourceWork
