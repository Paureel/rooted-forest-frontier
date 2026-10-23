import FullOutputCaller
import SourceValidity
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem partition_nonempty_member (L : List Nat) (P : List (List Nat)) (part : partitionCheck L P=true) :
 ∀A,A∈P→A≠[] := by
 have p:=part;simp only [partitionCheck,Bool.and_eq_true] at p
 intro A aP empty
 have good:=List.all_eq_true.mp p.1.1 A aP
 simp [empty] at good

theorem partition_member_labels (L : List Nat) (P : List (List Nat)) (part : partitionCheck L P=true) :
 ∀A,A∈P→∀x,x∈A→x∈L := by
 have p:=part;simp only [partitionCheck,Bool.and_eq_true] at p
 intro A aP x xA
 exact List.contains_iff_mem.mp (List.all_eq_true.mp p.2 x (List.mem_flatten.mpr ⟨A,aP,xA⟩))

theorem three_distinct_members_length {α : Type} (P : List α) (A B C : α)
 (a : A∈P) (b : B∈P) (c : C∈P) (ab : A≠B) (ac : A≠C) (bc : B≠C) : 3≤P.length := by
 cases P with
 | nil => simp at a
 | cons D rest =>
  cases rest with
  | nil =>
   have ea : A=D := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using a
   have eb : B=D := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using b
   exact False.elim (ab (ea.trans eb.symm))
  | cons E rest =>
   cases rest with
   | nil =>
    have aa : A=D ∨ A=E := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using a
    have bb : B=D ∨ B=E := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using b
    have cc : C=D ∨ C=E := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using c
    rcases aa with aa|aa <;> rcases bb with bb|bb <;> rcases cc with cc|cc
    · exact False.elim (ab (aa.trans bb.symm))
    · exact False.elim (ab (aa.trans bb.symm))
    · exact False.elim (ac (aa.trans cc.symm))
    · exact False.elim (bc (bb.trans cc.symm))
    · exact False.elim (bc (bb.trans cc.symm))
    · exact False.elim (ac (aa.trans cc.symm))
    · exact False.elim (ab (aa.trans bb.symm))
    · exact False.elim (ab (aa.trans bb.symm))
   | cons H rest => simp only [List.length_cons];omega

theorem monochromatic_partition_three (S : Tree) (P : List (List Nat)) (color : Nat→Nat)
 (nd : (leaves S).Nodup) (part : partitionCheck (leaves S) P=true)
 (mono : ∀K,K∈P→LabelMonochromatic color K) (x y z : Nat)
 (xL : x∈leaves S) (yL : y∈leaves S) (zL : z∈leaves S)
 (xy : color x≠color y) (xz : color x≠color z) (yz : color y≠color z) : 3≤P.length := by
 have flat:=IndependentCommon.flatten_from_partition _ P nd part
 obtain ⟨A,aP,xA⟩:=List.mem_flatten.mp (flat.mem_iff.mpr xL)
 obtain ⟨B,bP,yB⟩:=List.mem_flatten.mp (flat.mem_iff.mpr yL)
 obtain ⟨C,cP,zC⟩:=List.mem_flatten.mp (flat.mem_iff.mpr zL)
 apply three_distinct_members_length P A B C aP bP cP
 · intro eq;subst B;exact xy (mono A aP x y xA yB)
 · intro eq;subst C;exact xz (mono A aP x z xA zC)
 · intro eq;subst C;exact yz (mono B bP y z yB zC)

theorem literal_tagged_colors_distinct (A B C : List Nat) (ca cb cc : Nat→Nat) (x y z : Nat)
 (apart : (∀x,x∈A→x∈B→False) ∧ (∀x,x∈A→x∈C→False) ∧ (∀x,x∈B→x∈C→False))
 (xA : x∈A) (yB : y∈B) (zC : z∈C) :
 taggedColor A B ca cb cc x≠taggedColor A B ca cb cc y ∧
 taggedColor A B ca cb cc x≠taggedColor A B ca cb cc z ∧
 taggedColor A B ca cb cc y≠taggedColor A B ca cb cc z := by
 have ya : y∉A := fun h=>apart.1 y h yB
 have za : z∉A := fun h=>apart.2.1 z h zC
 have zb : z∉B := fun h=>apart.2.2 z h zC
 simp only [taggedColor,ite_eq_left xA,ite_eq_right ya,ite_eq_left yB,ite_eq_right za,ite_eq_right zb]
 omega

theorem whole_source_payment (T S : Tree) (A B C : List Nat) (q : Nat) (ca cb cc : Nat→Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (o : Output) (member : o∈wholeOutputs S A B ca cb cc q) (real : CutRealization.RealizedOutput S o) :
 partitionCheck (leaves S) o.partition=true ∧ pairwiseEmbeddings S o.partition=true ∧
 o.partition.length=o.sourceCuts.length+1 ∧ 2≤o.sourceCuts.length := by
 have valid:=Assembly.generated_source_valid S (taggedColor A B ca cb cc) q o member
 have mono:=CutRealization.generate_monochromatic S (taggedColor A B ca cb cc) q o member
 have nonempty:=partition_nonempty_member _ _ part
 obtain ⟨x,xA⟩:=List.exists_mem_of_ne_nil A (nonempty A (by simp))
 obtain ⟨y,yB⟩:=List.exists_mem_of_ne_nil B (nonempty B (by simp))
 obtain ⟨z,zC⟩:=List.exists_mem_of_ne_nil C (nonempty C (by simp))
 have labels:=partition_member_labels _ _ part
 have colors:=literal_tagged_colors_distinct A B C ca cb cc x y z (partition_parent_apart _ _ _ _ part) xA yB zC
 have bound:=monochromatic_partition_three S o.partition (taggedColor A B ca cb cc)
  (IndependentReconstruction.proper_parts proper).2.1 valid.1 mono x y z
  (labels A (by simp) x xA) (labels B (by simp) y yB) (labels C (by simp) z zC) colors.1 colors.2.1 colors.2.2
 obtain ⟨_,_,components,_,_,_,_,_,_,_,payment⟩:=real
 exact ⟨valid.1,valid.2,payment,by omega⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.partition_nonempty_member
#print axioms ContactedHard2Survival.partition_nonempty_member
#check @ContactedHard2Survival.partition_member_labels
#print axioms ContactedHard2Survival.partition_member_labels
#check @ContactedHard2Survival.three_distinct_members_length
#print axioms ContactedHard2Survival.three_distinct_members_length
#check @ContactedHard2Survival.monochromatic_partition_three
#print axioms ContactedHard2Survival.monochromatic_partition_three
#check @ContactedHard2Survival.literal_tagged_colors_distinct
#print axioms ContactedHard2Survival.literal_tagged_colors_distinct
#check @ContactedHard2Survival.whole_source_payment
#print axioms ContactedHard2Survival.whole_source_payment
