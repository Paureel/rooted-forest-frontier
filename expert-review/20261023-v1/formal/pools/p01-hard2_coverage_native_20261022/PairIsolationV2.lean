import PairReconstructionV2
open RMAF ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedGoodPair

theorem clear_subsets (t : Tree) (P Q U V : List Nat)
 (clear : Clear (minimalVertices U t) (minimalVertices V t)) (pU : P⊆U) (qV : Q⊆V) :
 Clear (minimalVertices P t) (minimalVertices Q t) := by
 intro v hp hq
 exact clear v (VertexGeometry.executable_span_monotone t P U pU v hp)
  (VertexGeometry.executable_span_monotone t Q V qV v hq)

theorem isolated_source_cross (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (ac : Clear (minimalVertices A T) (minimalVertices C T))
 (bc : Clear (minimalVertices B T) (minimalVertices C T)) :
 CrossClear (some T) (OutputState.sourceForest S [A,B,C]) [A++B,C] := by
 have scope:=ContactedHard2DP.pair_source_scope T S A B C proper part emb
 have nd:=checked_family_nodup _ _ scope.2.1
 have ne : A++B≠C := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.nodup_cons.mp nd).1
 have mat:=OutputState.checked_materialization S [A,B,C] (IndependentReconstruction.proper_parts proper).2.1 part
 have base : ∀s,s∈owned (OutputState.sourceForest S [A,B,C]) (A++B)→
  ∀r,r∈owned (OutputState.sourceForest S [A,B,C]) C→
   Clear (minimalVertices (leaves s) T) (minimalVertices (leaves r) T) := by
  intro s hs r hr
  have sm:=(mem_owned s _ _).1 hs
  have rm:=(mem_owned r _ _).1 hr
  obtain ⟨D,hD,_,perm,_,nonempty⟩:=mat.2.2 s sm.1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hD
  rcases hD with e|e|e <;> subst D
  · exact clear_subsets T _ _ A C ac (fun x hx=>perm.mem_iff.1 hx) rm.2
  · exact clear_subsets T _ _ B C bc (fun x hx=>perm.mem_iff.1 hx) rm.2
  · obtain ⟨x,hx⟩:=List.exists_mem_of_ne_nil _ nonempty
    exact False.elim (ne (ForestGroups.group_unique _ _ scope.2.1 (A++B) C
      List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) x (sm.2 hx) (perm.mem_iff.1 hx)))
 intro t et U hU V hV diff s hs r hr
 have et' : T=t := Option.some.inj et
 subst t
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hU hV
 rcases hU with e|e <;> subst U <;> rcases hV with e|e <;> subst V
 · exact False.elim (diff rfl)
 · exact base s hs r hr
 · exact (clear_symm _ _).2 (base r hr s hs)
 · exact False.elim (diff rfl)

theorem pair_complete_isolated (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (ac : Clear (minimalVertices A T) (minimalVertices C T))
 (bc : Clear (minimalVertices B T) (minimalVertices C T))
 (goodA : restrictionAgrees S T A=true) (goodB : restrictionAgrees S T B=true)
 (below : PaidInstances.BelowBudget ordinary q)
 (F : Forest) (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q) :
 ∃G,(runPair (PaidInstances.OwnPaid ordinary q) T S A B C q).answer=some G ∧
 agreement T S G=true ∧ VertexGeometry.Refines G [A,B,C] ∧ G.length≤F.length := by
 exact pair_complete ordinary q T S A B C proper part emb
  (isolated_source_cross T S A B C proper part emb ac bc) goodA goodB below F agree ref budget
end ContactedGoodPair

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedGoodPair.clear_subsets
#print axioms ContactedGoodPair.clear_subsets
#check @ContactedGoodPair.isolated_source_cross
#print axioms ContactedGoodPair.isolated_source_cross
#check @ContactedGoodPair.pair_complete_isolated
#print axioms ContactedGoodPair.pair_complete_isolated
