import GoodEdgeCollapse
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
open IndependentOneExchange
namespace ContactedHard2Survival

theorem good_edge_exchange (T S : Tree) (A B C : List Nat) (e : RMAF.Vertex×RMAF.Vertex) (F : List (List Nat))
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (sourceEmb : pairwiseEmbeddings S [A,B,C]=true)
 (clearAC : ContactedHard2Overlap.Clear T A C) (clearEdge : PairGeometry.ActualClear T A B e.2)
 (edge : e∈PairGeometry.edges T) (sides : ∀inside,PairGeometry.sideLabels A T e.2 inside≠[])
 (good : restrictionAgrees S T A=true) (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) :
 ∃J,agreement T S J=true ∧ VertexGeometry.Refines J [A,B,C] ∧ J.length≤F.length ∧
 ParentMono J B (sideColor (PairGeometry.descendants T e.2)) := by
 obtain ⟨U,subtree⟩:=edge_child_subtree T e edge
 have labels:=descendants_child_clade T U e.2 (IndependentReconstruction.proper_parts proper).1 subtree
 let H:=splitForest (leaves U) F
 have split:=ContactedClade.original_clade_split_full (ContactedForward.proper_swap_own proper) subtree
  (IndependentGeometry.agreement_swap agree)
 have agreeH : agreement T S H=true:=IndependentGeometry.agreement_swap split.1
 have refH : VertexGeometry.Refines H [A,B,C]:=split_refines_parents (leaves U) F [A,B,C] ref
 have colors : sideColor (PairGeometry.descendants T e.2)=sideColor (leaves U) := by
  funext x
  simp only [sideColor,labels x]
 have monoH : ∀K,K∈H→LabelMonochromatic (sideColor (PairGeometry.descendants T e.2)) K := by
  rw [colors]
  exact split_side_monochrome (leaves U) F
 obtain ⟨x,xSide⟩:=List.exists_mem_of_ne_nil (PairGeometry.sideLabels A T e.2 true) (sides true)
 obtain ⟨y,ySide⟩:=List.exists_mem_of_ne_nil (PairGeometry.sideLabels A T e.2 false) (sides false)
 have xp:=List.mem_filter.mp xSide
 have yp:=List.mem_filter.mp ySide
 have xd : x∈PairGeometry.descendants T e.2 := by simpa using xp.2
 have yd : y∉PairGeometry.descendants T e.2 := by simpa using yp.2
 have two:=monochrome_family_two T S A B C (PairGeometry.descendants T e.2) H proper part agreeH refH monoH
  x y xp.1 yp.1 xd yd
 have collapsed:=good_edge_collapse T S A B C e.2 H proper part sourceEmb agreeH refH clearAC clearEdge monoH good two
 refine ⟨collapseParent A H,collapsed.1,collapsed.2.1,?_,collapsed.2.2.2⟩
 have lengthH : H.length≤F.length+1 :=split.2.1
 have decrease:=collapsed.2.2.1
 omega
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.good_edge_exchange
#print axioms ContactedHard2Survival.good_edge_exchange
