import PaidCaseExact
namespace OrdinaryDispatch.Hard2Dispatcher
open RMAF ForestState RestrictionBridge Universal233 Universal233.BothBad
open Universal233.CherryBranching Universal233.Hard2Overlap Universal233.PaidAssembly

theorem query_exact_from_contract (T S : Tree) (q : Nat) (answer : Option Forest)
 (sound : ∀F,answer=some F→agreement T S F=true ∧ F.length-1≤q)
 (complete : ∀F,agreement T S F=true→F.length-1≤q→∃G,answer=some G ∧ G.length≤F.length) :
 QueryExact T S q answer := by
 cases answer with
 | none =>
  intro F hf
  by_cases affordable : F.length-1≤q
  · obtain ⟨G,hG,_⟩ := complete F hf affordable
    contradiction
  · omega
 | some G =>
  have gs := sound G rfl
  refine ⟨gs.1,gs.2,?_⟩
  intro F hf
  by_cases affordable : F.length-1≤q
  · obtain ⟨H,hH,min⟩ := complete F hf affordable
    have eq : G=H := Option.some.inj hH
    simpa [eq] using min
  · omega

theorem rule5_exact (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b q : Nat}
 (ch : CoreGraph.CherryAt T i a b) (ad : Rule5Local.admitted T S a b=true) (below : BelowIH q actual) :
 QueryExact T S q (rule5Answer actual T S a b q) := by
 obtain ⟨answer,run,ex⟩ := Rule5OrdinaryDispatch.admitted_exact actual ch ad q below
 have eq : rule5Answer actual T S a b q=answer := by simp [rule5Answer,run]
 rw [eq]
 exact query_exact_from_contract T S q answer (fun F hF=>⟨(ex.1 F hF).1,(ex.1 F hF).2.1⟩) ex.2

theorem non_disjoint_exact (actual : Ordinary) {T S : Tree} {c : Candidate} {q : Nat} {out : Result}
 (proper : DepthOne.proper T S=true) (forward : CherryBranching.select T S=some (.hard2,c))
 (selected : runHard2 T S c=some out) (notDisjoint : out≠.disjoint) (below : BelowIH q actual) :
 QueryExact T S q (Hard2Combine.combine actual T S c.a c.b q (paidCase actual T S c q out)).answer := by
 have prop := OrdinaryPriorityBridge.proper_parts proper
 have ch := (selected_actual forward).1
 apply query_exact_from_contract T S q _
 · intro F hf
   exact Hard2Combine.combine_sound actual T S c.a c.b q _ (paidCase_sound actual T S c q out) F hf
 · intro F hf budget
   apply Hard2Combine.combine_complete actual T S c.a c.b q _ prop.1 prop.2.1
    (fun _=>prop.2.2.mem_iff) ch below
   · intro G hg href hbudget
     exact paidCase_complete actual proper forward selected notDisjoint below G hg href hbudget
   · exact hf
   · exact budget

/-- A complete literal hard2 dispatcher on the exact post-priority context.
No global ordinary IH or requested geometry is a premise. -/
theorem run_exact {actual : Ordinary} {T S : Tree} {c d : Candidate} {q : Nat}
 (proper : DepthOne.proper T S=true)
 (forward : CherryBranching.select T S=some (.hard2,c))
 (reverse : CherryBranching.select S T=some (.hard2,d))
 (noT : Rule4.select T S=none) (noS : Rule4.select S T=none)
 (rejected : DepthOne.pretest01 T S=.rejected) (below : BelowIH q actual) :
 QueryExact T S q (run actual T S c d q) := by
 obtain ⟨p,r,out,originalCutsEq,hcuts,graph,hp,es,selected,valid⟩ := actual_hard2_exhaustive proper forward
 have prop := OrdinaryPriorityBridge.proper_parts proper
 have same : ∀x,x∈leaves T ↔ x∈leaves S := fun _=>prop.2.2.mem_iff
 have ch := (selected_actual forward).1
 cases out with
 | disjoint =>
  have eqP := pendant_eq_literal hcuts
  have part : partitionCheck (leaves S) (pendantPartition S c.a c.b)=true := by rw [eqP];exact hp
  have source : pairwiseEmbeddings S (pendantPartition S c.a c.b)=true := by rw [eqP];exact es
  have target : pairwiseEmbeddings T (pendantPartition S c.a c.b)=true := by rw [eqP];exact valid
  by_cases good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=true
  · have exactness := DisjointParents.direct_exact T S (pendantPartition S c.a c.b) q same part target source good
     (by rw [eqP];rfl) rejected
    simpa [run,selected,good] using exactness
  · have badGood : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false := by
     cases h:(pendantPartition S c.a c.b).all (restrictionAgrees T S) <;> simp_all
    by_cases two : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2
    · have admitted := (actual_disjoint_admission_iff proper forward reverse noT noS selected).2 two
      have exactness := rule5_exact actual ch admitted below
      simpa [run,selected,badGood,two] using exactness
    · have twoCuts : (cuts S c.a c.b).length=2 := by rw [hcuts];rfl
      have exactness := query_exact_from_contract T S q (DisjointParents.run actual T S c.a c.b q)
       (DisjointParents.run_sound actual T S c.a c.b q)
       (DisjointParents.run_complete actual T S c.a c.b q prop.1 prop.2.1 same ch twoCuts target below)
      simpa [run,selected,badGood,two] using exactness
 | clique v =>
  simpa [run,selected] using non_disjoint_exact actual proper forward selected (by simp) below
 | four o v w =>
  simpa [run,selected] using non_disjoint_exact actual proper forward selected (by simp) below
 | diagonal o v w =>
  simpa [run,selected] using non_disjoint_exact actual proper forward selected (by simp) below
 | pair o choice =>
  simpa [run,selected] using non_disjoint_exact actual proper forward selected (by simp) below
end OrdinaryDispatch.Hard2Dispatcher
