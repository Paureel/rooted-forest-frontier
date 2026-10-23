import CgoodRetainedOutput
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem output_parent_scope (T S : Tree) (Q P : List (List Nat))
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) Q=true)
 (part : partitionCheck (leaves S) P=true) (emb : pairwiseEmbeddings S P=true)
 (ref : VertexGeometry.Refines P Q) :
 ForestState.proper (some T) (sourceForest S P)=true ∧ partitionCheck (leaves T) Q=true ∧ Owns (sourceForest S P) Q := by
 have pp:=IndependentReconstruction.proper_parts proper
 have mat:=checked_materialization S P pp.2.1 part
 refine ⟨(FreshResidual.residual_transfer_scope.1 T S P [] proper part emb).2.1,?_,?_⟩
 · exact (partition_labels_congr (leaves S) (leaves T) Q (fun _=>pp.2.2.mem_iff.symm)).mp parents
 · intro s hs
   obtain ⟨D,dP,_,perm,_,_⟩:=mat.2.2 s hs
   obtain ⟨U,uQ,sub⟩:=ref D dP
   exact ⟨U,uQ,fun x hx=>sub x (perm.mem_iff.mp hx)⟩

theorem retained_paid_B_call (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (A B C : List Nat) (o : Output) (below : PaidInstances.BelowBudget ordinary q)
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (part : partitionCheck (leaves S) o.partition=true) (emb : pairwiseEmbeddings S o.partition=true)
 (refP : VertexGeometry.Refines o.partition [A,B,C]) (payment : o.partition.length=o.sourceCuts.length+1)
 (oneA : (owned (sourceForest S o.partition) A).length=1)
 (oneC : (owned (sourceForest S o.partition) C).length=1)
 (F : List (List Nat)) (agree : agreement T S F=true) (refF : VertexGeometry.Refines F o.partition)
 (badA : restrictionAgrees S T A=false) (budget : F.length-1≤q) :
 o.sourceCuts.length+1≤q ∧ q-o.sourceCuts.length-1<q ∧
 additionalCost (owned (sourceForest S o.partition) B) (family B F)≤q-o.sourceCuts.length-1 ∧
 ∃G,GenericForest.solve (PaidInstances.OwnPaid ordinary q) (localTarget (some T) B)
  (owned (sourceForest S o.partition) B) (q-o.sourceCuts.length-1)=some G ∧
 agrees (localTarget (some T) B) (owned (sourceForest S o.partition) B) G=true ∧ G.length≤(family B F).length ∧
 2+G.length+1≤F.length := by
 let ss:=sourceForest S o.partition
 have scope:=output_parent_scope T S [A,B,C] o.partition proper parents part emb refP
 have refParents : VertexGeometry.Refines F [A,B,C] := by
  intro K kF
  obtain ⟨D,dP,sub⟩:=refF K kF
  obtain ⟨U,uQ,subU⟩:=refP D dP
  exact ⟨U,uQ,fun x hx=>subU x (sub x hx)⟩
 have fa : agrees (some T) ss F=true:=
  (FreshResidual.residual_transfer_scope.1 T S o.partition F proper part emb).2.2.mpr ⟨agree,refF⟩
 have localB:=local_forward (some T) ss [A,B,C] F fa scope.2.1 scope.2.2 B (by simp)
 have lowerB:=sources_le_blocks _ _ _ localB
 have sourceGroups:=source_group_lengths (some T) ss [A,B,C] scope.1 scope.2.1 scope.2.2
 have sourceLen:=(FreshResidual.residual_transfer_scope.1 T S o.partition F proper part emb).1
 have forestLen:=(three_family_perm A B C F (partition_parent_apart _ _ _ _ parents) refParents
  (agreement_nonempty T S F agree)).length_eq
 have twoA:=bad_parent_family_two T S [A,B,C] F A proper parents agree refParents (by simp) badA
 have permC:=parent_family_perm_any T S [A,B,C] F proper parents agree refParents C (by simp)
 have oneFamilyC:=flatten_perm_nonempty_length _ _ permC (partition_nonempty_member _ _ parents C (by simp))
 simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at sourceGroups
 simp only [List.length_append] at forestLen
 have affordable : o.sourceCuts.length+1≤q ∧ q-o.sourceCuts.length-1<q ∧
  additionalCost (owned ss B) (family B F)≤q-o.sourceCuts.length-1 := by
  dsimp only [ss] at sourceGroups lowerB ⊢
  unfold additionalCost
  omega
 obtain ⟨G,runG,least⟩:=PaidInstanceForest.forest_completion_obligation (q-o.sourceCuts.length-1)
  (PaidInstances.OwnPaid ordinary q) (PaidInstances.local_ordinary_ih ordinary q _ below affordable.2.1)
  (localTarget (some T) B) (owned ss B) (family B F) localB affordable.2.2
 have agreeG:=(GenericForest.solve_sound (PaidInstances.OwnPaid ordinary q) _ _ _ G runG).1
 exact ⟨affordable.1,affordable.2.1,affordable.2.2,G,runG,agreeG,least,by omega⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.output_parent_scope
#print axioms ContactedHard2Survival.output_parent_scope
#check @ContactedHard2Survival.retained_paid_B_call
#print axioms ContactedHard2Survival.retained_paid_B_call
