import RetainedDispatch
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

-- This premise is discharged only by the released original ordinaryExecution bridge
-- after explicit original callback instantiation and common-context checking.
def ParentExecutionContract (solve : BothBad.ForestSolver) (outer : Nat) : Prop :=
 ∀T S P b,DepthOne.proper T S=true→partitionCheck (leaves S) P=true→pairwiseEmbeddings S P=true→
  partitionCheck (leaves T) P=true→pairwiseEmbeddings T P=true→b<outer→
  ∀F,agreement T S F=true→VertexGeometry.Refines F P→F.length-P.length≤b→
  ∃G,(BothBad.ordinaryExecution solve T S P b).answer=some G ∧ agreement T S G=true ∧ G.length≤F.length

theorem literal_ordinary_dispatch_complete (solve : BothBad.ForestSolver) (q : Nat) (T S : Tree)
 (contract : ParentExecutionContract solve q) (proper : DepthOne.proper T S=true)
 (o : Output) (part : partitionCheck (leaves S) o.partition=true) (embS : pairwiseEmbeddings S o.partition=true)
 (embT : pairwiseEmbeddings T o.partition=true)
 (payment : o.partition.length=o.sourceCuts.length+1) (positive : 0<o.sourceCuts.length)
 (F : List (List Nat)) (agree : agreement T S F=true) (ref : VertexGeometry.Refines F o.partition)
 (budget : F.length-1≤q) : o.sourceCuts.length≤q ∧ q-o.sourceCuts.length<q ∧
 ∃G,BothBad.checked T S q (BothBad.dispatch solve T S ⟨o,.ordinary,q-o.sourceCuts.length⟩).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 have scope:=FreshResidual.residual_transfer_scope.1 T S o.partition F proper part embS
 have fa : agrees (some T) (sourceForest S o.partition) F=true:=scope.2.2.mpr ⟨agree,ref⟩
 have count:=sources_le_blocks _ _ _ fa
 rw [scope.1] at count
 have pp:=IndependentReconstruction.proper_parts proper
 have targetPart : partitionCheck (leaves T) o.partition=true:=
  (partition_labels_congr (leaves S) (leaves T) _ (fun _=>pp.2.2.mem_iff.symm)).mp part
 have paid : o.sourceCuts.length≤q ∧ q-o.sourceCuts.length<q ∧ F.length-o.partition.length≤q-o.sourceCuts.length:=by omega
 obtain ⟨G,runG,agreeG,least⟩:=contract T S o.partition (q-o.sourceCuts.length) proper part embS targetPart embT paid.2.1
  F agree ref paid.2.2
 have bg : G.length-1≤q:=by omega
 refine ⟨paid.1,paid.2.1,G,?_,agreeG,least⟩
 simp only [BothBad.dispatch,runG,BothBad.checked,Option.bind_some,BothBad.accept,agreeG,
  decide_eq_true bg,Bool.and_self,ite_true]
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.literal_ordinary_dispatch_complete
#print axioms ContactedHard2Survival.literal_ordinary_dispatch_complete
