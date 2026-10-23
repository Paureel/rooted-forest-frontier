import TwoColorFibers
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem original_joint_label_member (T : Tree) (B : List Nat) (v w : RMAF.Vertex)
 (nd : (leaves T).Nodup) (labels : ∀x,x∈B→x∈leaves T) (x : Nat) (xB : x∈B) :
 (colorLabel T v x,colorLabel T w x)∈jointColors B T v w := by
 obtain ⟨a,ha⟩:=(singleton_selected_exists T x).mpr (labels x xB)
 apply List.mem_eraseDups.mpr
 apply List.mem_map.mpr
 refine ⟨a,(leafList_correct B T a).mpr ((selected_decompose_label B T a).mpr ⟨x,xB,ha⟩),?_⟩
 change (region v a,region w a)=(colorLabel T v x,colorLabel T w x)
 rw [colorLabel_at_address T v x nd a ha,colorLabel_at_address T w x nd a ha]

theorem occupied_parent_nonconstant (T : Tree) (B : List Nat) (v : RMAF.Vertex)
 (nd : (leaves T).Nodup) (labels : ∀x,x∈B→x∈leaves T)
 (no : ¬selectedLeaves (leaves T) T v) (occupied : v∈minimalVertices B T) :
 ¬LabelMonochromatic (colorLabel T v) B := by
 have nb : ¬selectedLeaves B T v := fun h=>no (selected_mono_own B (leaves T) labels T v h)
 intro mono
 exact ((original_label_avoids_iff T B v nd labels nb).mpr mono) occupied

theorem diagonal_middle_fibers (T : Tree) (B : List Nat) (v w : RMAF.Vertex)
 (nd : (leaves T).Nodup) (labels : ∀x,x∈B→x∈leaves T)
 (vn : ¬selectedLeaves (leaves T) T v) (wn : ¬selectedLeaves (leaves T) T w)
 (vb : v∈minimalVertices B T) (wb : w∈minimalVertices B T)
 (two : (jointColors B T v w).length=2) :
 ∀x y,x∈B→y∈B→(colorLabel T v x=colorLabel T v y ↔ colorLabel T w x=colorLabel T w y) := by
 exact projection_two_fibers B (colorLabel T v) (colorLabel T w) (jointColors B T v w) two
  (original_joint_label_member T B v w nd labels)
  (occupied_parent_nonconstant T B v nd labels vn vb) (occupied_parent_nonconstant T B w nd labels wn wb)

theorem diagonal_parent_avoidance_coupling (T S : Tree) (B : List Nat) (v w : RMAF.Vertex) (F : List (List Nat))
 (proper : DepthOne.proper T S=true) (agree : agreement T S F=true) (labels : ∀x,x∈B→x∈leaves T)
 (vn : ¬selectedLeaves (leaves T) T v) (wn : ¬selectedLeaves (leaves T) T w)
 (vb : v∈minimalVertices B T) (wb : w∈minimalVertices B T)
 (two : (jointColors B T v w).length=2) : ParentAvoids T F B v ↔ ParentAvoids T F B w := by
 have nd:=(IndependentReconstruction.proper_parts proper).1
 have fibers:=diagonal_middle_fibers T B v w nd labels vn wn vb wb two
 have block : ∀K,K∈F→K⊆B→(v∉minimalVertices K T ↔ w∉minimalVertices K T) := by
  intro K kF sub
  have kl:=agreement_block_labels T S F agree K kF
  have nv : ¬selectedLeaves K T v := fun h=>vn (selected_mono_own K (leaves T) kl T v h)
  have nw : ¬selectedLeaves K T w := fun h=>wn (selected_mono_own K (leaves T) kl T w h)
  rw [original_label_avoids_iff T K v nd kl nv,original_label_avoids_iff T K w nd kl nw]
  constructor
  · intro mono x y hx hy
    exact (fibers x y (sub hx) (sub hy)).mp (mono x y hx hy)
  · intro mono x y hx hy
    exact (fibers x y (sub hx) (sub hy)).mpr (mono x y hx hy)
 constructor
 · intro avoid K kF sub;exact (block K kF sub).mp (avoid K kF sub)
 · intro avoid K kF sub;exact (block K kF sub).mpr (avoid K kF sub)

theorem diagonal_source_cover (T S : Tree) (A B C : List Nat) (q : Nat) (F : List (List Nat)) (v w : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q)
 (vn : ¬selectedLeaves (leaves T) T v) (wn : ¬selectedLeaves (leaves T) T w)
 (vb : v∈minimalVertices B T) (wb : w∈minimalVertices B T) (two : (jointColors B T v w).length=2) :
 ∃o,o∈diagonalOutputs S T A B v w q ∧ VertexGeometry.Refines F o.partition ∧ CutRealization.RealizedOutput S o := by
 have apart:=partition_parent_apart _ _ _ _ part
 have nonempty:=agreement_nonempty T S F agree
 have emb:=agreement_target_embedding T S F agree
 have ab:=two_parent_avoidance T F A B v nonempty emb apart.1
 have bc:=two_parent_avoidance T F B C w nonempty emb apart.2.2
 have blabels : ∀x,x∈B→x∈leaves T := by
  intro x hx
  exact (IndependentReconstruction.proper_parts proper).2.2.mem_iff.mpr (partition_member_labels _ _ part B (by simp) x hx)
 have couple:=diagonal_parent_avoidance_coupling T S B v w F proper agree blabels vn wn vb wb two
 have alternative : (ParentAvoids T F B v ∧ ParentAvoids T F B w) ∨ (ParentAvoids T F A v ∧ ParentAvoids T F C w) := by
  rcases ab with a|b
  · rcases bc with b|c
    · exact Or.inl ⟨couple.mpr b,b⟩
    · exact Or.inr ⟨a,c⟩
  · exact Or.inl ⟨b,couple.mp b⟩
 rcases alternative with h|h
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (fun _=>0) (jointLabel T v w) (fun _=>0) (constant_monochrome F A)
    (joint_monochrome T F B v w (avoidance_monochrome T S F B v proper agree vn h.1)
      (avoidance_monochrome T S F B w proper agree wn h.2)) (constant_monochrome F C)
   exact ⟨o,by simp only [diagonalOutputs,List.mem_append];exact Or.inl mem,refine,real⟩
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (colorLabel T v) (fun _=>0) (colorLabel T w) (avoidance_monochrome T S F A v proper agree vn h.1)
    (constant_monochrome F B) (avoidance_monochrome T S F C w proper agree wn h.2)
   exact ⟨o,by simp only [diagonalOutputs,List.mem_append];exact Or.inr mem,refine,real⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.original_joint_label_member
#print axioms ContactedHard2Survival.original_joint_label_member
#check @ContactedHard2Survival.occupied_parent_nonconstant
#print axioms ContactedHard2Survival.occupied_parent_nonconstant
#check @ContactedHard2Survival.diagonal_middle_fibers
#print axioms ContactedHard2Survival.diagonal_middle_fibers
#check @ContactedHard2Survival.diagonal_parent_avoidance_coupling
#print axioms ContactedHard2Survival.diagonal_parent_avoidance_coupling
#check @ContactedHard2Survival.diagonal_source_cover
#print axioms ContactedHard2Survival.diagonal_source_cover
