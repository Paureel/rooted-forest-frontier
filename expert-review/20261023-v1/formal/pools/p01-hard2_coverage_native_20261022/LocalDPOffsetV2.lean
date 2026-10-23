-- Exact A++B DP offset and competing C residual on the actual runPair state.
import LocalDPGuardsV2
open RMAF ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace ContactedHard2DP

theorem pair_source_scope (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true) :
 let ss:=sourceForest S [A,B,C]
 let Q:List (List Nat):=[A++B,C]
 ForestState.proper (some T) ss=true ∧ partitionCheck (ForestState.labels (some T)) Q=true ∧
 Owns ss Q ∧ ss.length=3 := by
 dsimp only
 have pp:=IndependentReconstruction.proper_parts proper
 have mat:=checked_materialization S [A,B,C] pp.2.1 part
 refine ⟨(FreshResidual.residual_transfer_scope.1 T S [A,B,C] [] proper part emb).2.1,?_,?_,by simpa using mat.1⟩
 · exact (partition_labels_congr (leaves S) (leaves T) _ (fun x=>pp.2.2.mem_iff.symm)).1
    (merge_first_two_check _ _ _ _ part)
 · intro s hs
   obtain ⟨D,hD,_,perm,_,_⟩:=mat.2.2 s hs
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hD
   rcases hD with e|e|e <;> subst D
   · exact ⟨A++B,List.mem_cons_self,fun x hx=>List.mem_append_left _ (perm.mem_iff.1 hx)⟩
   · exact ⟨A++B,List.mem_cons_self,fun x hx=>List.mem_append_right _ (perm.mem_iff.1 hx)⟩
   · exact ⟨C,List.mem_cons_of_mem _ List.mem_cons_self,fun x hx=>perm.mem_iff.1 hx⟩

theorem refinement_merge {F : List (List Nat)} {A B C : List Nat}
 (ref : VertexGeometry.Refines F [A,B,C]) : Refines F [A++B,C] := by
 intro D hD
 obtain ⟨U,hU,sub⟩:=ref D hD
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hU
 rcases hU with e|e|e <;> subst U
 · exact ⟨A++B,List.mem_cons_self,fun x hx=>List.mem_append_left _ (sub x hx)⟩
 · exact ⟨A++B,List.mem_cons_self,fun x hx=>List.mem_append_right _ (sub x hx)⟩
 · exact ⟨C,List.mem_cons_of_mem _ List.mem_cons_self,sub⟩

theorem local_offset_competitors (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (goodA : restrictionAgrees S T A=true) (goodB : restrictionAgrees S T B=true) :
 let ss:=sourceForest S [A,B,C]
 let left:=owned ss (A++B)
 let right:=owned ss C
 ∃H,AllGoodDP.run (localTarget (some T) (A++B)) left=some H ∧
 agrees (localTarget (some T) (A++B)) left H=true ∧
 additionalCost left H+left.length=H.length ∧
 ∀F,agreement T S F=true→VertexGeometry.Refines F [A,B,C]→
 agrees (localTarget (some T) (A++B)) left (family (A++B) F)=true ∧
 agrees (localTarget (some T) C) right (family C F)=true ∧
 additionalCost left H≤additionalCost left (family (A++B) F) ∧
 2+additionalCost left (family (A++B) F)+additionalCost right (family C F)=F.length-1 ∧
 H.length+(family C F).length≤F.length := by
 dsimp only
 let ss:=sourceForest S [A,B,C]
 let Q:List (List Nat):=[A++B,C]
 have scope:=pair_source_scope T S A B C proper part emb
 obtain ⟨H,runH,agreeH,idH,minH⟩:=AllGoodDP.run_total_exact _ _ (literal_pair_allGood T S A B C proper part emb goodA goodB)
 refine ⟨H,runH,agreeH,idH,?_⟩
 intro F agree ref
 have forestAgree : agrees (some T) ss F=true :=
   (FreshResidual.residual_transfer_scope.1 T S [A,B,C] F proper part emb).2.2.2 ⟨agree,ref⟩
 have left:=local_forward (some T) ss Q F forestAgree scope.2.1 scope.2.2.1 (A++B) List.mem_cons_self
 have right:=local_forward (some T) ss Q F forestAgree scope.2.1 scope.2.2.1 C (List.mem_cons_of_mem _ List.mem_cons_self)
 have min:=minH _ left
 have countF:=ForestState.agrees_parts _ _ _ forestAgree
 have lengthF:=total_family_length (ForestState.labels (some T)) F Q countF.2.1 scope.2.1 (refinement_merge ref)
 have lengthS:=source_group_lengths (some T) ss Q scope.1 scope.2.1 scope.2.2.1
 have boundL:=sources_le_blocks _ _ _ left
 have boundR:=sources_le_blocks _ _ _ right
 dsimp only [ss] at *
 simp only [Q,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at lengthF lengthS
 have base : 2+(F.length-3)=F.length-1 := by
  have child : feasible T S (makeChild S [A,B,C] 2) F := ⟨agree,ref⟩
  exact IndependentPaid.paid_identity (IndependentReconstruction.proper_parts proper).2.1 part rfl child
 refine ⟨left,right,min,?_,?_⟩
 · unfold additionalCost at *
   have lenSS:=scope.2.2.2
   omega
 · unfold additionalCost at min idH
   omega

theorem actual_remaining_C_call (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (goodA : restrictionAgrees S T A=true) (goodB : restrictionAgrees S T B=true)
 (below : PaidInstances.BelowBudget ordinary q)
 (F : List (List Nat)) (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C])
 (budget : F.length-1≤q) :
 let ss:=sourceForest S [A,B,C]
 ∃H K,AllGoodDP.run (localTarget (some T) (A++B)) (owned ss (A++B))=some H ∧
 let m:=additionalCost (owned ss (A++B)) H
 2≤q ∧ m≤q-2 ∧ q-2-m<q ∧
 GenericForest.solve (PaidInstances.OwnPaid ordinary q) (localTarget (some T) C) (owned ss C) (q-2-m)=some K ∧
 H.length+K.length≤F.length := by
 dsimp only
 obtain ⟨H,runH,_,_,comp⟩:=local_offset_competitors T S A B C proper part emb goodA goodB
 have bounds:=comp F agree ref
 let m:=additionalCost (owned (sourceForest S [A,B,C]) (A++B)) H
 have affordable : 2≤q ∧ m≤q-2 ∧ q-2-m<q ∧
   additionalCost (owned (sourceForest S [A,B,C]) C) (family C F)≤q-2-m := by
  have least:=bounds.2.2.1
  have pay:=bounds.2.2.2.1
  dsimp only [m]
  omega
 have ih:=PaidInstances.local_ordinary_ih ordinary q (q-2-m) below affordable.2.2.1
 obtain ⟨K,runK,leastK⟩:=PaidInstanceForest.forest_completion_obligation (q-2-m)
   (PaidInstances.OwnPaid ordinary q) ih (localTarget (some T) C) (owned (sourceForest S [A,B,C]) C)
   (family C F) bounds.2.1 affordable.2.2.2
 exact ⟨H,K,runH,affordable.1,affordable.2.1,affordable.2.2.1,runK,by have len:=bounds.2.2.2.2;omega⟩
end ContactedHard2DP

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2DP.pair_source_scope
#print axioms ContactedHard2DP.pair_source_scope
#check @ContactedHard2DP.refinement_merge
#print axioms ContactedHard2DP.refinement_merge
#check @ContactedHard2DP.local_offset_competitors
#print axioms ContactedHard2DP.local_offset_competitors
#check @ContactedHard2DP.actual_remaining_C_call
#print axioms ContactedHard2DP.actual_remaining_C_call
