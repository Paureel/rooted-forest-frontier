import CgoodPalette
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Survival

theorem contained_false_of_apart (K A B : List Nat) (ne : K≠[]) (sub : K⊆A)
 (apart : ∀x,x∈A→x∈B→False) : contained K B=false := by
 apply Bool.eq_false_iff.mpr
 intro yes
 obtain ⟨x,xK⟩:=List.exists_mem_of_ne_nil K ne
 exact apart x (sub xK) (List.contains_iff_mem.mp (List.all_eq_true.mp yes x xK))

theorem three_family_perm (A B C : List Nat) (F : List (List Nat))
 (apart : (∀x,x∈A→x∈B→False) ∧ (∀x,x∈A→x∈C→False) ∧ (∀x,x∈B→x∈C→False))
 (ref : VertexGeometry.Refines F [A,B,C]) (nonempty : ∀K,K∈F→K≠[]) :
 F.Perm (family A F++family B F++family C F) := by
 induction F with
 | nil=>exact List.Perm.refl _
 | cons K F ih=>
  have tailRef : VertexGeometry.Refines F [A,B,C]:=fun J hj=>ref J (List.mem_cons_of_mem K hj)
  have tailNe : ∀J,J∈F→J≠[]:=fun J hj=>nonempty J (List.mem_cons_of_mem K hj)
  have tail:=ih tailRef tailNe
  have ne:=nonempty K List.mem_cons_self
  obtain ⟨U,uP,sub⟩:=ref K List.mem_cons_self
  simp only [List.mem_cons,List.not_mem_nil,or_false] at uP
  rcases uP with eq|eq|eq <;>subst U
  · have ka:=contained_true_of_subset K A sub
    have kb:=contained_false_of_apart K A B ne sub apart.1
    have kc:=contained_false_of_apart K A C ne sub apart.2.1
    simpa only [family,List.filter_cons,ka,kb,kc,ite_true,Bool.false_eq_true,ite_false,List.cons_append]
     using List.Perm.cons K tail
  · have kb:=contained_true_of_subset K B sub
    have ka:=contained_false_of_apart K B A ne sub (fun x xb xa=>apart.1 x xa xb)
    have kc:=contained_false_of_apart K B C ne sub apart.2.2
    have moved:=(List.Perm.cons K tail).trans (by
     simpa only [List.append_assoc] using move_head_append K (family A F) (family B F++family C F))
    simpa only [family,List.filter_cons,ka,kb,kc,ite_true,Bool.false_eq_true,ite_false,List.cons_append,List.append_assoc]
     using moved
  · have kc:=contained_true_of_subset K C sub
    have ka:=contained_false_of_apart K C A ne sub (fun x xc xa=>apart.2.1 x xa xc)
    have kb:=contained_false_of_apart K C B ne sub (fun x xc xb=>apart.2.2 x xb xc)
    have moved:=(List.Perm.cons K tail).trans (by
     simpa only [List.append_assoc] using move_head_append K (family A F++family B F) (family C F))
    simpa only [family,List.filter_cons,ka,kb,kc,ite_true,Bool.false_eq_true,ite_false,List.cons_append,List.append_assoc]
     using moved

theorem parent_family_perm_any (T S : Tree) (P H : List (List Nat))
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) P=true)
 (agree : agreement T S H=true) (ref : VertexGeometry.Refines H P) (A : List Nat) (aP : A∈P) :
 (family A H).flatten.Perm A := by
 have pp:=IndependentReconstruction.proper_parts proper
 have targetPart : partitionCheck (leaves T) P=true :=
  (partition_labels_congr (leaves S) (leaves T) P (fun _=>pp.2.2.mem_iff.symm)).mp part
 obtain ⟨u,restriction,perm⟩:=OutputState.checked_restrictions T P pp.1 targetPart A aP
 have member : u∈OutputState.sourceForest T P:=List.mem_filterMap.mpr ⟨A,aP,restriction⟩
 have material:=OutputState.checked_materialization T P pp.1 targetPart
 obtain ⟨_,_,_,_,ndu,_⟩:=material.2.2 u member
 have familyCheck:=local_partition T u A H P restriction (by
  have checks:=agree;simp only [agreement,Bool.and_eq_true] at checks;exact checks.1.1.1.1) targetPart ref aP
 exact (IndependentCommon.flatten_from_partition _ (family A H) ndu familyCheck).trans perm

theorem pairwise_append_own (S : Tree) (P Q : List (List Nat))
 (p : pairwiseEmbeddings S P=true) (q : pairwiseEmbeddings S Q=true)
 (cross : ∀K,K∈P→∀J,J∈Q→disjointVertices (minimalVertices K S) (minimalVertices J S)=true) :
 pairwiseEmbeddings S (P++Q)=true := by
 induction P with
 | nil=>exact q
 | cons K P ih=>
  have pp:=p
  simp only [pairwiseEmbeddings,Bool.and_eq_true] at pp
  change (_ && _)=true
  simp only [Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro J member
    rcases List.mem_append.mp member with jp|jq
    · exact List.all_eq_true.mp pp.1 J jp
    · exact cross K List.mem_cons_self J jq
  · exact ih pp.2 (fun J jp U uq=>cross J (List.mem_cons_of_mem K jp) U uq)

theorem flatten_perm_nonempty_length (P : List (List Nat)) (A : List Nat)
 (perm : P.flatten.Perm A) (ne : A≠[]) : 1≤P.length := by
 cases P with
 | nil=>
  have length:=perm.length_eq
  have empty : A=[]:=List.eq_nil_of_length_eq_zero (by simpa only [List.flatten_nil,List.length_nil] using length.symm)
  exact False.elim (ne empty)
 | cons K P=>simp only [List.length_cons];omega

def retainedSource (A B C : List Nat) (F : List (List Nat)) : List (List Nat):=[A]++family B F++[C]

theorem retained_source_scope (T S : Tree) (A B C D : List Nat) (F : List (List Nat))
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true) (agree : agreement T S F=true)
 (ref : VertexGeometry.Refines F [A,B,C]) (mb : ParentMono F B (sideColor D)) :
 let J:=retainedSource A B C F
 partitionCheck (leaves S) J=true ∧ pairwiseEmbeddings S J=true ∧
 VertexGeometry.Refines F J ∧ VertexGeometry.Refines J [A,B,C] ∧ J.length≤F.length ∧
 (∀K,K∈J→LabelMonochromatic (edgeCheapColor B A D) K) := by
 dsimp only
 have ndS:=(IndependentReconstruction.proper_parts proper).2.1
 have apart:=partition_parent_apart _ _ _ _ part
 have nonempty:=partition_nonempty_member _ _ part
 have neA:=nonempty A (by simp)
 have neC:=nonempty C (by simp)
 have neF:=agreement_nonempty T S F agree
 have pa:=parent_family_perm_any T S [A,B,C] F proper part agree ref A (by simp)
 have pb:=parent_family_perm_any T S [A,B,C] F proper part agree ref B (by simp)
 have pc:=parent_family_perm_any T S [A,B,C] F proper part agree ref C (by simp)
 have permF:=three_family_perm A B C F apart ref neF
 have neJ : ∀K,K∈retainedSource A B C F→K≠[] := by
  intro K member
  simp only [retainedSource,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with eq|member|eq
  · subst K;exact neA
  · exact neF K (List.mem_filter.mp member).1
  · subst K;exact neC
 have permJ : (retainedSource A B C F).flatten.Perm (leaves S) := by
  have intermediate : (retainedSource A B C F).flatten.Perm [A,B,C].flatten := by
   simpa only [retainedSource,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
    using List.Perm.append (List.Perm.refl A) (List.Perm.append pb (List.Perm.refl C))
  exact intermediate.trans (IndependentCommon.flatten_from_partition _ [A,B,C] ndS part)
 have partJ:=IndependentCommon.partition_from_flatten _ _ ndS neJ permJ
 have familyEmb : pairwiseEmbeddings S (family B F)=true:=
  IndependentGeometry.pairwise_filter S F (fun K=>contained K B) (agreement_source_embedding T S F agree)
 have checks:=emb
 simp only [pairwiseEmbeddings,Bool.and_eq_true] at checks
 have ab:=List.all_eq_true.mp checks.1 B (by simp)
 have ac:=List.all_eq_true.mp checks.1 C (by simp)
 have bc:=List.all_eq_true.mp checks.2.1 C (by simp)
 have subB : ∀K,K∈family B F→K⊆B:=fun K member=>(contained_iff K B).mp (List.mem_filter.mp member).2
 have embAB:=pairwise_append_own S [A] (family B F) (by rfl) familyEmb (by
  intro K member J jB
  have eq : K=A:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
  subst K
  exact ContactedClade.disjoint_subsets S (fun _ hx=>hx) (fun _ hx=>subB J jB hx) ab)
 have embJ:=pairwise_append_own S ([A]++family B F) [C] embAB (by rfl) (by
  intro K member J jC
  have eq : J=C:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using jC
  subst J
  rcases List.mem_append.mp member with a|b
  · have eq : K=A:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using a
    subst K;exact ac
  · exact ContactedClade.disjoint_subsets S (fun _ hx=>subB K b hx) (fun _ hx=>hx) bc)
 have refF : VertexGeometry.Refines F (retainedSource A B C F) := by
  intro K kF
  obtain ⟨U,uP,sub⟩:=ref K kF
  simp only [List.mem_cons,List.not_mem_nil,or_false] at uP
  rcases uP with eq|eq|eq <;>subst U
  · exact ⟨A,by dsimp only [retainedSource];exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self),sub⟩
  · exact ⟨K,by
      change K∈A::(family B F++[C])
      exact List.mem_cons_of_mem A (List.mem_append_left _ (List.mem_filter.mpr ⟨kF,contained_true_of_subset K B sub⟩)),fun _ hx=>hx⟩
  · exact ⟨C,by dsimp only [retainedSource];exact List.mem_append_right _ List.mem_cons_self,sub⟩
 have refJ : VertexGeometry.Refines (retainedSource A B C F) [A,B,C] := by
  intro K member
  simp only [retainedSource,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with eq|b|eq
  · subst K;exact ⟨A,by simp,fun _ hx=>hx⟩
  · exact ⟨B,by simp,subB K b⟩
  · subst K;exact ⟨C,by simp,fun _ hx=>hx⟩
 have least : (retainedSource A B C F).length≤F.length := by
  have oneA:=flatten_perm_nonempty_length _ _ pa neA
  have oneC:=flatten_perm_nonempty_length _ _ pc neC
  have len:=permF.length_eq
  simp only [retainedSource,List.length_append,List.length_cons,List.length_nil] at len ⊢
  omega
 have monoB : ParentMono (retainedSource A B C F) B (sideColor D) := by
  intro K member sub
  simp only [retainedSource,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with eq|b|eq
  · subst K
    obtain ⟨x,xA⟩:=List.exists_mem_of_ne_nil A neA
    exact False.elim (apart.1 x xA (sub xA))
  · exact mb K (List.mem_filter.mp b).1 sub
  · subst K
    obtain ⟨x,xC⟩:=List.exists_mem_of_ne_nil C neC
    exact False.elim (apart.2.2 x (sub xC) xC)
 refine ⟨partJ,?_,refF,refJ,least,?_⟩
 · simpa only [retainedSource,List.append_assoc] using embJ
 · exact tagged_monochrome _ A B C _ _ _ refJ apart.1 apart.2.1 apart.2.2
    (constant_monochrome _ A) monoB (constant_monochrome _ C)
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.contained_false_of_apart
#print axioms ContactedHard2Survival.contained_false_of_apart
#check @ContactedHard2Survival.three_family_perm
#print axioms ContactedHard2Survival.three_family_perm
#check @ContactedHard2Survival.parent_family_perm_any
#print axioms ContactedHard2Survival.parent_family_perm_any
#check @ContactedHard2Survival.pairwise_append_own
#print axioms ContactedHard2Survival.pairwise_append_own
#check @ContactedHard2Survival.flatten_perm_nonempty_length
#print axioms ContactedHard2Survival.flatten_perm_nonempty_length
#check @ContactedHard2Survival.retained_source_scope
#print axioms ContactedHard2Survival.retained_source_scope
