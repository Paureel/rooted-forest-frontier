import RetainedKnownParts
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233
namespace ContactedHard2Survival

theorem retained_output_cross (T S : Tree) (A B C : List Nat) (P : List (List Nat)) (p : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) P=true)
 (monoB : ParentMono P B (sideColor (PairGeometry.descendants T p)))
 (clearAB : PairGeometry.ActualClear T A B p)
 (clearAC : Clear (minimalVertices A T) (minimalVertices C T))
 (clearBC : Clear (minimalVertices B T) (minimalVertices C T)) :
 CrossClear (some T) (sourceForest S P) [A,B,C] := by
 have mat:=checked_materialization S P (IndependentReconstruction.proper_parts proper).2.1 part
 have ab : ∀s,s∈owned (sourceForest S P) A→∀r,r∈owned (sourceForest S P) B→
   Clear (minimalVertices (leaves s) T) (minimalVertices (leaves r) T) := by
  intro s hs r hr
  have sm:=(mem_owned s _ _).mp hs
  have rm:=(mem_owned r _ _).mp hr
  obtain ⟨D,dP,_,labels,_,ne⟩:=mat.2.2 r rm.1
  have dSub : D⊆B:=fun x hx=>rm.2 (labels.mem_iff.mpr hx)
  have mono : LabelMonochromatic (sideColor (PairGeometry.descendants T p)) (leaves r) := by
   intro x y hx hy
   exact monoB D dP dSub x y (labels.mem_iff.mp hx) (labels.mem_iff.mp hy)
  obtain ⟨inside,region⟩:=side_monochrome_in_region T B (leaves r) p ne rm.2 mono
  intro v vs vr
  exact clearAB.2 inside v (ContactedClade.minimal_subset T (fun _ hx=>region hx) v vr)
    (ContactedClade.minimal_subset T (fun _ hx=>sm.2 hx) v vs)
 have ac : ∀s,s∈owned (sourceForest S P) A→∀r,r∈owned (sourceForest S P) C→
   Clear (minimalVertices (leaves s) T) (minimalVertices (leaves r) T) := by
  intro s hs r hr
  exact ContactedGoodPair.clear_subsets T _ _ A C clearAC (mem_owned s _ _ |>.mp hs).2 (mem_owned r _ _ |>.mp hr).2
 have bc : ∀s,s∈owned (sourceForest S P) B→∀r,r∈owned (sourceForest S P) C→
   Clear (minimalVertices (leaves s) T) (minimalVertices (leaves r) T) := by
  intro s hs r hr
  exact ContactedGoodPair.clear_subsets T _ _ B C clearBC (mem_owned s _ _ |>.mp hs).2 (mem_owned r _ _ |>.mp hr).2
 intro t ht U uQ V vQ diff s hs r hr
 have eq : T=t:=Option.some.inj ht
 subst t
 simp only [List.mem_cons,List.not_mem_nil,or_false] at uQ vQ
 rcases uQ with eq|eq|eq <;>subst U <;>rcases vQ with eq|eq|eq <;>subst V
 · exact False.elim (diff rfl)
 · exact ab s hs r hr
 · exact ac s hs r hr
 · exact (clear_symm _ _).mpr (ab r hr s hs)
 · exact False.elim (diff rfl)
 · exact bc s hs r hr
 · exact (clear_symm _ _).mpr (ac r hr s hs)
 · exact (clear_symm _ _).mpr (bc r hr s hs)
 · exact False.elim (diff rfl)

theorem retained_assemble (T S : Tree) (A B C : List Nat) (P J : List (List Nat))
 (p : RMAF.Vertex) (known G : List (List Nat))
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (part : partitionCheck (leaves S) P=true) (emb : pairwiseEmbeddings S P=true)
 (refP : VertexGeometry.Refines P [A,B,C]) (refJ : VertexGeometry.Refines J P)
 (aJ : A∈J) (cJ : C∈J) (knownRun : BothBad.knownOne T S A=some known)
 (goodC : restrictionAgrees S T C=true)
 (localB : agrees (localTarget (some T) B) (owned (sourceForest S P) B) G=true)
 (monoB : ParentMono P B (sideColor (PairGeometry.descendants T p)))
 (clearAB : PairGeometry.ActualClear T A B p)
 (clearAC : Clear (minimalVertices A T) (minimalVertices C T))
 (clearBC : Clear (minimalVertices B T) (minimalVertices C T)) :
 agreement T S (known++G++[C])=true ∧ VertexGeometry.Refines (known++G++[C]) P ∧ known.length=2 := by
 have scope:=output_parent_scope T S [A,B,C] P proper parents part emb refP
 have localA:=retained_knownOne_local T S [A,B,C] P J A known proper parents part emb refP refJ
  (by simp) aJ knownRun
 have localC:=retained_good_parent_local T S [A,B,C] P J C proper parents part emb refP refJ
  (by simp) cJ goodC
 have nd:=checked_family_nodup _ _ parents
 have ab : A≠B:=by intro h;exact (List.nodup_cons.mp nd).1 (by simp [h])
 have ac : A≠C:=by intro h;exact (List.nodup_cons.mp nd).1 (by simp [h])
 have bc : B≠C:=by intro h;exact (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])
 let chosen : List Nat→List (List Nat):=fun U=>if U=A then known else if U=B then G else [C]
 have locals : ∀U,U∈[A,B,C]→agrees (localTarget (some T) U) (owned (sourceForest S P) U) (chosen U)=true := by
  intro U member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq|eq|eq <;>subst U
  · simpa only [chosen,ite_true] using localA.1
  · simpa only [chosen,ite_eq_right (Ne.symm ab),ite_true] using localB
  · simpa only [chosen,ite_eq_right (Ne.symm ac),ite_eq_right (Ne.symm bc)] using localC
 have glued:=reverse_reconstruction (some T) (sourceForest S P) [A,B,C] chosen scope.1 scope.2.1 scope.2.2
  (retained_output_cross T S A B C P p proper part monoB clearAB clearAC clearBC) locals
 have actual : [A,B,C].flatMap chosen=known++G++[C] := by
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,chosen,ite_true,
   ite_eq_right (Ne.symm ab),ite_eq_right (Ne.symm ac),ite_eq_right (Ne.symm bc),List.append_assoc]
 rw [actual] at glued
 exact ⟨((FreshResidual.residual_transfer_scope.1 T S P _ proper part emb).2.2.mp glued).1,
  ((FreshResidual.residual_transfer_scope.1 T S P _ proper part emb).2.2.mp glued).2,localA.2⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.retained_output_cross
#print axioms ContactedHard2Survival.retained_output_cross
#check @ContactedHard2Survival.retained_assemble
#print axioms ContactedHard2Survival.retained_assemble
