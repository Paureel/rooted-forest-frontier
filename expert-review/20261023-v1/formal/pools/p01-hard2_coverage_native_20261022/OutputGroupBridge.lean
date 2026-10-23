import TaggedOutputScope
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233
namespace ContactedHard2Survival

theorem output_group_cross (T S : Tree) (A B C : List Nat) (P : List (List Nat))
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (part : partitionCheck (leaves S) P=true) (emb : pairwiseEmbeddings S P=true)
 (ref : VertexGeometry.Refines P [A,B,C])
 (ac : Clear (minimalVertices A T) (minimalVertices C T))
 (bc : Clear (minimalVertices B T) (minimalVertices C T)) :
 CrossClear (some T) (sourceForest S P) [A++B,C] := by
 have scope:=output_group_scope T S A B C P proper parents part emb ref
 have nd:=checked_family_nodup _ _ scope.2.1
 have ne : A++B≠C := by
  simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.nodup_cons.mp nd).1
 have mat:=checked_materialization S P (IndependentReconstruction.proper_parts proper).2.1 part
 have base : ∀s,s∈owned (sourceForest S P) (A++B)→∀r,r∈owned (sourceForest S P) C→
  Clear (minimalVertices (leaves s) T) (minimalVertices (leaves r) T) := by
  intro s hs r hr
  have sm:=(mem_owned s _ _).mp hs
  have rm:=(mem_owned r _ _).mp hr
  obtain ⟨D,dP,_,perm,_,nonempty⟩:=mat.2.2 s sm.1
  obtain ⟨U,uParent,sub⟩:=ref D dP
  simp only [List.mem_cons,List.not_mem_nil,or_false] at uParent
  rcases uParent with eq|eq|eq <;>subst U
  · exact ContactedGoodPair.clear_subsets T _ _ A C ac (fun _ hx=>sub _ (perm.mem_iff.mp hx)) rm.2
  · exact ContactedGoodPair.clear_subsets T _ _ B C bc (fun _ hx=>sub _ (perm.mem_iff.mp hx)) rm.2
  · obtain ⟨x,hx⟩:=List.exists_mem_of_ne_nil _ nonempty
    exact False.elim (ne (group_unique _ _ scope.2.1 (A++B) C (by simp) (by simp) x
     (sm.2 hx) (sub _ (perm.mem_iff.mp hx))))
 intro t et U uQ V vQ diff s hs r hr
 have eq : T=t:=Option.some.inj et
 subst t
 simp only [List.mem_cons,List.not_mem_nil,or_false] at uQ vQ
 rcases uQ with eq|eq <;>subst U <;>rcases vQ with eq|eq <;>subst V
 · exact False.elim (diff rfl)
 · exact base s hs r hr
 · exact (clear_symm _ _).mpr (base r hr s hs)
 · exact False.elim (diff rfl)

theorem output_group_costs (T S : Tree) (A B C : List Nat) (P : List (List Nat)) (cuts : Nat)
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (part : partitionCheck (leaves S) P=true) (emb : pairwiseEmbeddings S P=true)
 (refP : VertexGeometry.Refines P [A,B,C]) (payment : P.length=cuts+1)
 (F : List (List Nat)) (agree : agreement T S F=true) (refF : VertexGeometry.Refines F P) :
 let ss:=sourceForest S P
 agrees (localTarget (some T) (A++B)) (owned ss (A++B)) (family (A++B) F)=true ∧
 agrees (localTarget (some T) C) (owned ss C) (family C F)=true ∧
 cuts+additionalCost (owned ss (A++B)) (family (A++B) F)+
  additionalCost (owned ss C) (family C F)=F.length-1 := by
 dsimp only
 let ss:=sourceForest S P
 have scope:=output_group_scope T S A B C P proper parents part emb refP
 have fa : agrees (some T) ss F=true :=
  (FreshResidual.residual_transfer_scope.1 T S P F proper part emb).2.2.mpr ⟨agree,refF⟩
 have left:=local_forward (some T) ss [A++B,C] F fa scope.2.1 scope.2.2 (A++B) (by simp)
 have right:=local_forward (some T) ss [A++B,C] F fa scope.2.1 scope.2.2 C (by simp)
 have refParents : VertexGeometry.Refines F [A,B,C] := by
  intro K kF
  obtain ⟨D,dP,sub⟩:=refF K kF
  obtain ⟨U,uP,subU⟩:=refP D dP
  exact ⟨U,uP,fun _ hx=>subU _ (sub _ hx)⟩
 have lenF:=total_family_length (ForestState.labels (some T)) F [A++B,C]
  (ForestState.agrees_parts _ _ _ fa).2.1 scope.2.1 (ContactedHard2DP.refinement_merge refParents)
 have lenS:=source_group_lengths (some T) ss [A++B,C] scope.1 scope.2.1 scope.2.2
 have sourceLen:= (FreshResidual.residual_transfer_scope.1 T S P F proper part emb).1
 have bound:=sources_le_blocks _ _ _ fa
 have boundL:=sources_le_blocks _ _ _ left
 have boundR:=sources_le_blocks _ _ _ right
 simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at lenF lenS
 refine ⟨left,right,?_⟩
 unfold additionalCost
 dsimp only [ss] at *
 omega
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.output_group_cross
#print axioms ContactedHard2Survival.output_group_cross
#check @ContactedHard2Survival.output_group_costs
#print axioms ContactedHard2Survival.output_group_costs
