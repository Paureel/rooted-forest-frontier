import RetainedWholeParents
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem source_palette_lower (L : List Nat) (P : List (List Nat)) (color : Nat→Nat) (palette : List Nat)
 (nd : L.Nodup) (part : partitionCheck L P=true) (mono : ∀K,K∈P→LabelMonochromatic color K)
 (paletteND : palette.Nodup) (witness : ∀c,c∈palette→∃x,x∈L ∧ color x=c) : palette.length≤P.length := by
 let blockColor:=fun K=>color (colorRepresentative K)
 have flat:=IndependentCommon.flatten_from_partition L P nd part
 have sub : palette⊆P.map blockColor := by
  intro c hc
  obtain ⟨x,xL,xc⟩:=witness c hc
  obtain ⟨K,kP,xK⟩:=List.mem_flatten.mp (flat.mem_iff.mpr xL)
  have rep:=colorRepresentative_mem K (partition_nonempty_member L P part K kP)
  exact List.mem_map.mpr ⟨K,kP,(mono K kP _ x rep xK).trans xc⟩
 simpa only [List.length_map] using paletteND.length_le_of_subset sub

theorem retained_opposite_output (T S : Tree) (A B C D : List Nat) (q : Nat) (F : List (List Nat))
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (swapped : partitionCheck (leaves S) [B,A,C]=true) (emb : pairwiseEmbeddings S [A,B,C]=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C])
 (mb : ParentMono F B (sideColor D)) (budget : F.length-1≤q)
 (x y : Nat) (xB : x∈B) (yB : y∈B) (xd : x∈D) (yn : y∉D) :
 3≤q ∧ ∃o,o∈BothBad.reuse S (edgeCheapColor B A D) (generate S (edgeCheapColor B A D) 3).outputs q ∧
 CutRealization.RealizedOutput S o ∧ partitionCheck (leaves S) o.partition=true ∧
 pairwiseEmbeddings S o.partition=true ∧ VertexGeometry.Refines F o.partition ∧
 VertexGeometry.Refines o.partition [A,B,C] ∧
 (family A o.partition).length=1 ∧ (family C o.partition).length=1 ∧
 (owned (sourceForest S o.partition) A).length=1 ∧ (owned (sourceForest S o.partition) C).length=1 ∧
 VertexGeometry.Refines (retainedSource A B C F) o.partition ∧ ParentMono o.partition B (sideColor D) := by
 have ndS:=(IndependentReconstruction.proper_parts proper).2.1
 let J:=retainedSource A B C F
 have sourceJ:=retained_source_scope T S A B C D F proper parents emb agree ref mb
 have budgetJ : J.length-1≤q := by
  have least:=sourceJ.2.2.2.2.1
  change J.length≤F.length at least
  omega
 have lower:=source_palette_lower (leaves S) J (edgeCheapColor B A D) [0,1,2,4] ndS sourceJ.1
  sourceJ.2.2.2.2.2 (by decide) (cheap_four_palette S B A C D swapped x y xB yB xd yn)
 have qThree : 3≤q:=by simp only [List.length_cons,List.length_nil] at lower;omega
 have selection : ∃o,o∈BothBad.reuse S (edgeCheapColor B A D) (generate S (edgeCheapColor B A D) 3).outputs q ∧
  VertexGeometry.Refines J o.partition ∧ CutRealization.RealizedOutput S o ∧
  partitionCheck (leaves S) o.partition=true ∧ pairwiseEmbeddings S o.partition=true ∧
  VertexGeometry.Refines o.partition [A,B,C] := by
  let probe:=(generate S (edgeCheapColor B A D) 3).outputs
  by_cases empty : (generate S (edgeCheapColor B A D) 3).outputs.isEmpty=true
  · obtain ⟨o,member,refine,real⟩:=CutRealization.generate_refinement_coverage S J (edgeCheapColor B A D)
     ndS sourceJ.1 sourceJ.2.1 sourceJ.2.2.2.2.2 q budgetJ
    have source:=Assembly.generated_source_valid S (edgeCheapColor B A D) q o member
    have parentRef:=tagged_output_refines T S A B C (fun _=>0) (sideColor D) (fun _=>0) q proper parents o member
    exact ⟨o,by delta BothBad.reuse;rw [ite_eq_left empty];exact member,refine,real,source.1,source.2,parentRef⟩
  · have probeNe : probe≠[]:=fun eq=>empty (by change probe.isEmpty=true;rw [eq];rfl)
    obtain ⟨o,member⟩:=List.exists_mem_of_ne_nil probe probeNe
    have sat:=cheap_probe_saturation S B A C D swapped ndS x y xB yB xd yn o member
    have parentRef:=tagged_output_refines T S A B C (fun _=>0) (sideColor D) (fun _=>0) 3 proper parents o member
    exact ⟨o,by delta BothBad.reuse;rw [ite_eq_right empty];exact member,
     sat.2.2.2.2 J sourceJ.1 sourceJ.2.2.2.2.2,sat.1,sat.2.1,sat.2.2.1,parentRef⟩
 obtain ⟨o,member,refJ,real,partO,embO,refO⟩:=selection
 have ne:=partition_nonempty_member _ _ parents
 have oneA:=whole_parent_family_one (leaves S) o.partition [A,B,C] J A ndS partO parents refO refJ
  (by simp) (by dsimp only [J,retainedSource];exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)) (ne A (by simp))
 have oneC:=whole_parent_family_one (leaves S) o.partition [A,B,C] J C ndS partO parents refO refJ
  (by simp) (by dsimp only [J,retainedSource];exact List.mem_append_right _ List.mem_cons_self) (ne C (by simp))
 have actual : ∀U,U∈o.partition→∃s,restrict U S=some s ∧ (leaves s).Perm U:=fun U uP=>
  checked_restrictions S o.partition ndS partO U uP
 have countA:=materialized_owned_count S o.partition A actual
 have countC:=materialized_owned_count S o.partition C actual
 have colorMono : ∀K,K∈o.partition→LabelMonochromatic (edgeCheapColor B A D) K := by
  have genMember:=member
  change o∈(if (generate S (edgeCheapColor B A D) 3).outputs.isEmpty then
   (generate S (edgeCheapColor B A D) q).outputs else (generate S (edgeCheapColor B A D) 3).outputs) at genMember
  split at genMember
  · exact CutRealization.generate_monochromatic S (edgeCheapColor B A D) q o genMember
  · exact CutRealization.generate_monochromatic S (edgeCheapColor B A D) 3 o genMember
 have parentMono : ParentMono o.partition B (sideColor D) := by
  intro K kP subB x y hx hy
  have xa : x∉A:=fun h=>(partition_parent_apart _ _ _ _ parents).1 x h (subB hx)
  have ya : y∉A:=fun h=>(partition_parent_apart _ _ _ _ parents).1 y h (subB hy)
  have eq:=colorMono K kP x y hx hy
  simp only [edgeCheapColor,taggedColor,ite_eq_right xa,ite_eq_right ya,ite_eq_left (subB hx),ite_eq_left (subB hy)] at eq
  omega
 refine ⟨qThree,o,member,real,partO,embO,?_,refO,oneA,oneC,countA.trans oneA,countC.trans oneC,refJ,parentMono⟩
 intro K kF
 obtain ⟨U,uJ,sub⟩:=sourceJ.2.2.1 K kF
 obtain ⟨V,vP,subV⟩:=refJ U uJ
 exact ⟨V,vP,fun x hx=>subV x (sub x hx)⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.source_palette_lower
#print axioms ContactedHard2Survival.source_palette_lower
#check @ContactedHard2Survival.retained_opposite_output
#print axioms ContactedHard2Survival.retained_opposite_output
