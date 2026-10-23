import ColorSaturation
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

def edgeCheapColor (A B D : List Nat) : Nat→Nat:=taggedColor B A (fun _=>0) (sideColor D) (fun _=>0)

theorem literal_cheapColor (A B D : List Nat) : edgeCheapColor A B D=BinaryCheap.cheapColor A B D := by rfl

theorem cheap_four_palette (S : Tree) (A B C D : List Nat)
 (parents : partitionCheck (leaves S) [A,B,C]=true) (x y : Nat)
 (xA : x∈A) (yA : y∈A) (xd : x∈D) (yn : y∉D) :
 ∀c,c∈([0,1,2,4] : List Nat)→∃z,z∈leaves S ∧ edgeCheapColor A B D z=c := by
 have apart:=partition_parent_apart _ _ _ _ parents
 have nonempty:=partition_nonempty_member _ _ parents
 have labels:=partition_member_labels _ _ parents
 obtain ⟨b,bB⟩:=List.exists_mem_of_ne_nil B (nonempty B (by simp))
 obtain ⟨z,zC⟩:=List.exists_mem_of_ne_nil C (nonempty C (by simp))
 have xb : x∉B:=fun h=>apart.1 x xA h
 have yb : y∉B:=fun h=>apart.1 y yA h
 have zb : z∉B:=fun h=>apart.2.2 z h zC
 have za : z∉A:=fun h=>apart.2.1 z h zC
 have colorB : edgeCheapColor A B D b=0 := by simp only [edgeCheapColor,taggedColor,ite_eq_left bB]
 have colorX : edgeCheapColor A B D x=1 := by simp only [edgeCheapColor,taggedColor,ite_eq_right xb,ite_eq_left xA,sideColor,ite_eq_left xd]
 have colorY : edgeCheapColor A B D y=4 := by simp only [edgeCheapColor,taggedColor,ite_eq_right yb,ite_eq_left yA,sideColor,ite_eq_right yn]
 have colorZ : edgeCheapColor A B D z=2 := by simp only [edgeCheapColor,taggedColor,ite_eq_right zb,ite_eq_right za]
 intro c member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with eq|eq|eq|eq <;>subst c
 · exact ⟨b,labels B (by simp) b bB,colorB⟩
 · exact ⟨x,labels A (by simp) x xA,colorX⟩
 · exact ⟨z,labels C (by simp) z zC,colorZ⟩
 · exact ⟨y,labels A (by simp) y yA,colorY⟩

theorem cheap_probe_saturation (S : Tree) (A B C D : List Nat)
 (parents : partitionCheck (leaves S) [A,B,C]=true) (nd : (leaves S).Nodup)
 (x y : Nat) (xA : x∈A) (yA : y∈A) (xd : x∈D) (yn : y∉D)
 (o : Output) (member : o∈(generate S (edgeCheapColor A B D) 3).outputs) :
 CutRealization.RealizedOutput S o ∧ partitionCheck (leaves S) o.partition=true ∧
 pairwiseEmbeddings S o.partition=true ∧ o.partition.length≤4 ∧
 ∀F,partitionCheck (leaves S) F=true→(∀K,K∈F→LabelMonochromatic (edgeCheapColor A B D) K)→VertexGeometry.Refines F o.partition := by
 have real:=CutRealization.generate_original_realization S (edgeCheapColor A B D) 3 o member
 have source:=Assembly.generated_source_valid S (edgeCheapColor A B D) 3 o member
 have mono:=CutRealization.generate_monochromatic S (edgeCheapColor A B D) 3 o member
 have cutBound:=CutRealization.generate_cost_bound S (edgeCheapColor A B D) 3 o member
 have realCopy:=real
 obtain ⟨_,_,_,_,_,_,_,_,_,_,payment⟩:=realCopy
 have lengthBound : o.partition.length≤4:=by omega
 refine ⟨real,source.1,source.2,lengthBound,?_⟩
 intro F partF monoF
 exact saturated_color_refinement (leaves S) o.partition F (edgeCheapColor A B D) [0,1,2,4] nd
  source.1 partF mono monoF (by decide) (cheap_four_palette S A B C D parents x y xA yA xd yn) lengthBound
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.literal_cheapColor
#print axioms ContactedHard2Survival.literal_cheapColor
#check @ContactedHard2Survival.cheap_four_palette
#print axioms ContactedHard2Survival.cheap_four_palette
#check @ContactedHard2Survival.cheap_probe_saturation
#print axioms ContactedHard2Survival.cheap_probe_saturation
