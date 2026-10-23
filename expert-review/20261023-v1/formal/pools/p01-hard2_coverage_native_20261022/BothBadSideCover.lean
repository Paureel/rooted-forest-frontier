import GoodEdgeExchange
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
open IndependentOneExchange
namespace ContactedHard2Survival

theorem not_side_monochrome_crosses (D K : List Nat)
 (no : ¬LabelMonochromatic (sideColor D) K) : Crosses D K := by
 have inside : ∃x,x∈K ∧ x∈D := by
  apply Classical.byContradiction
  intro absent
  apply no
  intro x y hx hy
  have nx : x∉D := fun h=>absent ⟨x,hx,h⟩
  have ny : y∉D := fun h=>absent ⟨y,hy,h⟩
  simp only [sideColor,ite_eq_right nx,ite_eq_right ny]
 have outside : ∃x,x∈K ∧ x∉D := by
  apply Classical.byContradiction
  intro absent
  apply no
  intro x y hx hy
  have dx : x∈D := Classical.byContradiction (fun h=>absent ⟨x,hx,h⟩)
  have dy : y∈D := Classical.byContradiction (fun h=>absent ⟨y,hy,h⟩)
  simp only [sideColor,ite_eq_left dx,ite_eq_left dy]
 exact ⟨inside,outside⟩

theorem side_parent_alternative (T S : Tree) (A B : List Nat)
 (e : RMAF.Vertex×RMAF.Vertex) (F : List (List Nat))
 (proper : DepthOne.proper T S=true) (agree : agreement T S F=true)
 (apart : ∀x,x∈A→x∈B→False) (edge : e∈PairGeometry.edges T) :
 ParentMono F A (sideColor (PairGeometry.descendants T e.2)) ∨
 ParentMono F B (sideColor (PairGeometry.descendants T e.2)) := by
 let D:=PairGeometry.descendants T e.2
 obtain ⟨U,subtree⟩:=edge_child_subtree T e edge
 have labels:=descendants_child_clade T U e.2 (IndependentReconstruction.proper_parts proper).1 subtree
 have crossConvert : ∀K,Crosses D K→Crosses (leaves U) K := by
  intro K h
  obtain ⟨⟨x,xK,xd⟩,⟨y,yK,yd⟩⟩:=h
  exact ⟨⟨x,xK,(labels x).mp xd⟩,⟨y,yK,fun h=>yd ((labels y).mpr h)⟩⟩
 by_cases ma : ParentMono F A (sideColor D)
 · exact Or.inl ma
 · apply Or.inr
   have witness : ∃K,K∈F ∧ K⊆A ∧ ¬LabelMonochromatic (sideColor D) K := by
    apply Classical.byContradiction
    intro absent
    apply ma
    intro K kF sub
    exact Classical.byContradiction (fun no=>absent ⟨K,kF,sub,no⟩)
   obtain ⟨K,kF,subA,noK⟩:=witness
   intro L lF subB
   apply Classical.byContradiction
   intro noL
   have crossK:=not_side_monochrome_crosses D K noK
   have crossL:=not_side_monochrome_crosses D L noL
   have eq:=one_crossing_block subtree (agreement_target_embedding T S F agree)
    (agreement_block_labels T S F agree) kF lF (crossConvert K crossK) (crossConvert L crossL)
   obtain ⟨x,xK,_⟩:=crossK.1
   exact apart x (subA xK) (subB (eq ▸ xK))

theorem bothbad_source_cover (T S : Tree) (A B C : List Nat) (q : Nat)
 (e : RMAF.Vertex×RMAF.Vertex) (F : List (List Nat))
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C])
 (budget : F.length-1≤q) (edge : e∈PairGeometry.edges T)
 (swapPart : partitionCheck (leaves S) [B,A,C]=true) :
 ∃o,o∈(sideOutputs S B A (PairGeometry.descendants T e.2) q ++
          sideOutputs S A B (PairGeometry.descendants T e.2) q) ∧
 VertexGeometry.Refines F o.partition ∧ CutRealization.RealizedOutput S o := by
 have apart:=partition_parent_apart _ _ _ _ part
 have alternative:=side_parent_alternative T S A B e F proper agree apart.1 edge
 rcases alternative with ma|mb
 · have refSwap : VertexGeometry.Refines F [B,A,C] := by
    intro K kF
    obtain ⟨J,jP,sub⟩:=ref K kF
    exact ⟨J,(List.Perm.swap B A [C]).mem_iff.mp jP,sub⟩
   obtain ⟨o,member,refine,real⟩:=whole_source_cover T S B A C q F proper swapPart agree refSwap budget
    (fun _=>0) (sideColor (PairGeometry.descendants T e.2)) (fun _=>0)
    (constant_monochrome F B) ma (constant_monochrome F C)
   exact ⟨o,List.mem_append.mpr (Or.inl member),refine,real⟩
 · obtain ⟨o,member,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (fun _=>0) (sideColor (PairGeometry.descendants T e.2)) (fun _=>0)
    (constant_monochrome F A) mb (constant_monochrome F C)
   exact ⟨o,List.mem_append.mpr (Or.inr member),refine,real⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.not_side_monochrome_crosses
#print axioms ContactedHard2Survival.not_side_monochrome_crosses
#check @ContactedHard2Survival.side_parent_alternative
#print axioms ContactedHard2Survival.side_parent_alternative
#check @ContactedHard2Survival.bothbad_source_cover
#print axioms ContactedHard2Survival.bothbad_source_cover
