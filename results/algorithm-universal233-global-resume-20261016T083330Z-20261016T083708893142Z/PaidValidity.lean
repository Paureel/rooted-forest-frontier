import ActualPaid
namespace Universal233.Hard2PaidLocal
open RMAF CoreProgram SourceCoverage VertexGeometry BothBad BothBadLocal PaidAssembly Hard2Overlap Integration CherryBranching OrdinaryPriorityBridge

def OutputFacts (S : Tree) (q : Nat) (o : Output) : Prop :=
 partitionCheck (leaves S) o.partition=true ∧ pairwiseEmbeddings S o.partition=true ∧
 CutRealization.RealizedOutput S o ∧ o.partition.length=o.sourceCuts.length+1 ∧
 2≤o.sourceCuts.length ∧ o.sourceCuts.length≤q

theorem case_output_facts {S T : Tree} {A B C : List Nat} {q : Nat} {o : Output} (out : Result)
 (hs : (leaves S).Nodup) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (mem : o∈caseOutputs S T A B C q out) : OutputFacts S q o := by
 cases out with
 | disjoint => simp [caseOutputs] at mem
 | clique v => exact generated_output_facts (.clique v) hs hp mem
 | four order v w => exact generated_output_facts (.four v w) hs (permuted_partition order hp) mem
 | diagonal order v w => exact generated_output_facts (.diagonal v w) hs (permuted_partition order hp) mem
 | pair order choice =>
  have pp:=permuted_partition order hp
  cases choice with
  | vertex v => exact generated_output_facts (.vertex v) hs pp mem
  | edge e =>
   change o∈edgeOutputs S T _ _ e q at mem
   by_cases good : restrictionAgrees S T (first order A B C)=true
   · simp only [edgeOutputs,good,ite_true] at mem
     exact generated_output_facts (T:=T) (.side _) hs pp mem
   · simp only [edgeOutputs,good,Bool.false_eq_true,ite_false] at mem
     exact generated_output_facts (T:=T) (.side _) hs (BinaryCheap.partition_swap _ _ _ _ pp) mem

theorem actual_output_facts {T S : Tree} {c : Candidate} {q : Nat} {o : Output} (out : Result)
 (proper : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (mem : o∈actualOutputs S T c q out) : OutputFacts S q o := by
 obtain ⟨p,r,cuts,_,_,hp,_,_⟩:=actual_source_inputs proper hard
 obtain ⟨_,hs,_⟩:=proper_parts proper
 simp only [actualOutputs,cuts] at mem
 exact case_output_facts out hs hp mem

theorem actual_paid_full_source_call {T S : Tree} {c : Candidate} (out : Result) (q : Nat)
 (actual : Ordinary) (proper : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (call : Call) (mem : call∈(runHardPaid actual T S q c out).calls) :
 ∃o,o∈actualOutputs S T c q out ∧ OutputFacts S q o ∧ call.target=some T ∧
 call.sources=OutputState.sourceForest S o.partition ∧ call.budget+o.sourceCuts.length=q := by
 obtain ⟨o,ho,target,sources,payment⟩:=actual_paid_full_payment actual T S q c out call mem
 exact ⟨o,ho,actual_output_facts out proper hard ho,target,sources,payment⟩
end Universal233.Hard2PaidLocal
