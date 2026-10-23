import GroupedOutputAnswerBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState ForestGroups Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.GroupedFullQuery Universal233.PaidQueries Universal233.Rule5SelectedLocalWork

def groupedEvaluationCoefficient (N : Nat):=groupRunOutputPolynomial N+4*N+58

theorem groupEvaluateLocalSource_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (A B C : List Nat) (q : Nat) (os : List CoreProgram.Output) (N : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N)
 (shape:∀o,o∈os→o.sourceCuts.length≤N ∧ o.partition.length≤N ∧ ∀U,U∈o.partition→U.length≤N) :
 (groupEvaluateLocalSource actual T S A B C q os).work≤groupedEvaluationCoefficient N*os.length+2 ∧
 (groupEvaluateLocalSource actual T S A B C q os).value.candidates.length≤os.length ∧
 (groupEvaluateLocalSource actual T S A B C q os).value.queries.length≤2*os.length ∧
 (∀F,F∈(groupEvaluateLocalSource actual T S A B C q os).value.candidates→F.length≤2*N ∧ F.flatten.length≤4*N):=by
 induction os with
 | nil=>simp [groupEvaluateLocalSource]
 | cons o os ih=>
   have h:=shape o (by simp)
   have tail:=ih (by intro p hm;exact shape p (by simp [hm]))
   have run:=groupRunOutputLocalSource_bound actual T S A B C q o N tn sn al bl cl h.1 h.2.1 h.2.2
   have answer:=groupRunOutput_answer_bounds actual T S A B C q o N tn sn h.2.1
   let r:=groupRunOutputLocalSource actual T S A B C q o
   let a:=groupOutputAnswerMeter r.value
   have len:a.value.toList.length≤1:=by cases ha:a.value <;> simp
   have payload:∀F,F∈a.value.toList→F.length≤2*N ∧ F.flatten.length≤4*N:=by
    intro F hm
    cases ha:a.value with
    | none=>simp only [ha,Option.toList_none,List.not_mem_nil] at hm
    | some G=>
      have eq:F=G:=by simpa only [ha,Option.toList_some,List.mem_cons,List.not_mem_nil,or_false] using hm
      subst F
      exact answer.2.2 G ha
   have rr:r.work≤groupRunOutputPolynomial N:=run
   have aa:a.work≤4*N+34:=answer.1
   have tt:r.value.trace.length≤2:=answer.2.1
   have tailBill:(groupEvaluateLocalSource actual T S A B C q os).work≤
     (groupRunOutputPolynomial N+4*N+58)*os.length+2:=tail.1
   simp only [groupEvaluateLocalSource,List.length_append,List.length_cons]
   refine ⟨?_,?_,?_,?_⟩
   · change r.work+a.work+(groupEvaluateLocalSource actual T S A B C q os).work+2*r.value.trace.length+20≤_
     unfold groupedEvaluationCoefficient
     rw [Nat.mul_add,Nat.mul_one]
     omega
   · change a.value.toList.length+(groupEvaluateLocalSource actual T S A B C q os).value.candidates.length≤_
     omega
   · change r.value.trace.length+(groupEvaluateLocalSource actual T S A B C q os).value.queries.length≤_
     omega
   · intro F hm
     rcases List.mem_append.1 hm with ha|ht
     · exact payload F ha
     · exact tail.2.2.2 F ht
end OrdinaryDispatch.Hard2SourceWork
