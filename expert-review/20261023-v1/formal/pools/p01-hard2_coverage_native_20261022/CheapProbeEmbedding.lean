import CheapKnownOne
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem one_list_members_equal {α : Type} (L : List α) (one : L.length=1) (x y : α) (hx : x∈L) (hy : y∈L) : x=y := by
 cases L with
 | nil=>simp at hx
 | cons z rest=>
  have restNil : rest=[]:=List.eq_nil_of_length_eq_zero (by simpa only [List.length_cons] using Nat.succ.inj one)
  subst rest
  have xz : x=z:=by simpa using hx
  have yz : y=z:=by simpa using hy
  exact xz.trans yz.symm

theorem embedding_distinct_clear (T : Tree) (P : List (List Nat)) (emb : pairwiseEmbeddings T P=true)
 (K J : List Nat) (kP : K∈P) (jP : J∈P) (diff : K≠J) :
 Clear (minimalVertices K T) (minimalVertices J T) := by
 induction P with
 | nil=>simp at kP
 | cons U P ih=>
  have fields:=emb
  simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true] at fields
  rcases List.mem_cons.mp kP with eqK|kTail
  · subst K
    rcases List.mem_cons.mp jP with eqJ|jTail
    · exact False.elim (diff eqJ.symm)
    · exact (clear_iff _ _).mp (fields.1 J jTail)
  · rcases List.mem_cons.mp jP with eqJ|jTail
    · subst J
      exact (clear_symm _ _).mpr ((clear_iff _ _).mp (fields.1 K kTail))
    · exact ih fields.2 kTail jTail

theorem cheap_probe_BC_one (T S : Tree) (A B C : List Nat) (p : RMAF.Vertex)
 (parents : partitionCheck (leaves S) [A,B,C]=true) (parentsSwap : partitionCheck (leaves S) [B,A,C]=true)
 (nd : (leaves S).Nodup) (x y : Nat) (xA : x∈A) (yA : y∈A)
 (xd : x∈PairGeometry.descendants T p) (yn : y∉PairGeometry.descendants T p)
 (o : Output) (member : o∈(generate S (edgeCheapColor A B (PairGeometry.descendants T p)) 3).outputs) :
 (family A o.partition).length=2 ∧ (family B o.partition).length=1 ∧ (family C o.partition).length=1 := by
 let D:=PairGeometry.descendants T p
 have scope:=cheap_probe_saturation S A B C D parents nd x y xA yA xd yn o member
 have mono:=CutRealization.generate_monochromatic S (edgeCheapColor A B D) 3 o member
 have ref:=probe_source_refines T S A B C p o.partition parentsSwap nd scope.2.1 mono
 obtain ⟨K,kP,xK⟩:=checked_covers _ _ scope.2.1 (partition_member_labels _ _ parents A (by simp) x xA)
 obtain ⟨J,jP,yJ⟩:=checked_covers _ _ scope.2.1 (partition_member_labels _ _ parents A (by simp) y yA)
 have kA:=parent_of_label _ _ parents _ ref A K (by simp) kP x xK xA
 have jA:=parent_of_label _ _ parents _ ref A J (by simp) jP y yJ yA
 have diff : K≠J:=by
  intro eq
  subst J
  have same:=(cheap_A_color_iff A B D (partition_parent_apart _ _ _ _ parents).1 x y xA yA).mp (mono K kP x y xK yJ)
  have xdD : x∈D:=xd
  have ynD : y∉D:=yn
  simp only [sideColor,ite_eq_left xdD,ite_eq_right ynD] at same
  cases same
 have pairND : [K,J].Nodup:=by simp only [List.nodup_cons,List.nodup_nil,List.mem_cons,List.not_mem_nil,or_false];exact ⟨diff,by simp⟩
 have lower : 2≤(family A o.partition).length:=by
  have h:=pairND.length_le_of_subset (l₂:=family A o.partition) (by
   intro U hu
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
   rcases hu with eq|eq <;>subst U
   · exact (family_members_fresh K A o.partition).mpr ⟨kP,kA⟩
   · exact (family_members_fresh J A o.partition).mpr ⟨jP,jA⟩)
  exact h
 have bpos:=checked_parent_family_positive _ [A,B,C] o.partition B parents scope.2.1 ref (by simp)
 have cpos:=checked_parent_family_positive _ [A,B,C] o.partition C parents scope.2.1 ref (by simp)
 have total:=(three_family_perm A B C o.partition (partition_parent_apart _ _ _ _ parents) ref
  (partition_nonempty_member _ _ scope.2.1)).length_eq
 simp only [List.length_append] at total
 have bound:=scope.2.2.2.1
 omega

theorem cheap_probe_target_embedding (T S : Tree) (A B C : List Nat) (e : RMAF.Vertex×RMAF.Vertex)
 (proper : DepthOne.proper T S=true)
 (parents : partitionCheck (leaves S) [A,B,C]=true) (parentsSwap : partitionCheck (leaves S) [B,A,C]=true)
 (edge : e∈PairGeometry.edges T) (x y : Nat) (xA : x∈A) (yA : y∈A)
 (xd : x∈PairGeometry.descendants T e.2) (yn : y∉PairGeometry.descendants T e.2)
 (o : Output) (member : o∈(generate S (edgeCheapColor A B (PairGeometry.descendants T e.2)) 3).outputs)
 (clearAB : PairGeometry.ActualClear T A B e.2)
 (clearAC : Clear (minimalVertices A T) (minimalVertices C T))
 (clearBC : Clear (minimalVertices B T) (minimalVertices C T)) : pairwiseEmbeddings T o.partition=true := by
 have pp:=IndependentReconstruction.proper_parts proper
 let D:=PairGeometry.descendants T e.2
 have scope:=cheap_probe_saturation S A B C D parents pp.2.1 x y xA yA xd yn o member
 have mono:=CutRealization.generate_monochromatic S (edgeCheapColor A B D) 3 o member
 have ref:=probe_source_refines T S A B C e.2 o.partition parentsSwap pp.2.1 scope.2.1 mono
 have fibers:=cheap_probe_A_fibers T S A B C e.2 parents pp.2.1 x y xA yA xd yn o member
 have counts:=cheap_probe_BC_one T S A B C e.2 parents parentsSwap pp.2.1 x y xA yA xd yn o member
 have ae:=fiber_clade_embedding T S A o.partition e pp.1 scope.2.1 edge fibers
 have crossAB : ∀K,K∈o.partition→K⊆A→∀J,J∈o.partition→J⊆B→Clear (minimalVertices K T) (minimalVertices J T) := by
  intro K kP kA J jP jB
  obtain ⟨inside,labels⟩:=fibers K ((family_members_fresh K A o.partition).mpr ⟨kP,kA⟩)
  intro v vk vj
  exact clearAB.1 inside v (ContactedClade.minimal_subset T (fun z hz=>(labels z).mp hz) v vk)
   (ContactedClade.minimal_subset T (fun _ hz=>jB hz) v vj)
 have nd:=checked_family_nodup _ _ scope.2.1
 apply (pairwise_iff T o.partition).mpr
 apply List.Pairwise.imp_of_mem (l:=o.partition) (R:=fun K J=>K≠J) (S:=fun K J=>Clear (minimalVertices K T) (minimalVertices J T)) _ nd
 intro K J kP jP diff
 obtain ⟨U,uParent,kSub⟩:=ref K kP
 obtain ⟨V,vParent,jSub⟩:=ref J jP
 simp only [List.mem_cons,List.not_mem_nil,or_false] at uParent vParent
 rcases uParent with eq|eq|eq <;>subst U <;>rcases vParent with eq|eq|eq <;>subst V
 · exact embedding_distinct_clear T (family A o.partition) ae K J
    ((family_members_fresh K A _).mpr ⟨kP,kSub⟩) ((family_members_fresh J A _).mpr ⟨jP,jSub⟩) diff
 · exact crossAB K kP kSub J jP jSub
 · exact ContactedGoodPair.clear_subsets T K J A C clearAC kSub jSub
 · exact (clear_symm _ _).mpr (crossAB J jP jSub K kP kSub)
 · exact False.elim (diff (one_list_members_equal (family B o.partition) counts.2.1 K J
    ((family_members_fresh K B _).mpr ⟨kP,kSub⟩) ((family_members_fresh J B _).mpr ⟨jP,jSub⟩)))
 · exact ContactedGoodPair.clear_subsets T K J B C clearBC kSub jSub
 · exact (clear_symm _ _).mpr (ContactedGoodPair.clear_subsets T J K A C clearAC jSub kSub)
 · exact (clear_symm _ _).mpr (ContactedGoodPair.clear_subsets T J K B C clearBC jSub kSub)
 · exact False.elim (diff (one_list_members_equal (family C o.partition) counts.2.2 K J
    ((family_members_fresh K C _).mpr ⟨kP,kSub⟩) ((family_members_fresh J C _).mpr ⟨jP,jSub⟩)))
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.one_list_members_equal
#print axioms ContactedHard2Survival.one_list_members_equal
#check @ContactedHard2Survival.embedding_distinct_clear
#print axioms ContactedHard2Survival.embedding_distinct_clear
#check @ContactedHard2Survival.cheap_probe_BC_one
#print axioms ContactedHard2Survival.cheap_probe_BC_one
#check @ContactedHard2Survival.cheap_probe_target_embedding
#print axioms ContactedHard2Survival.cheap_probe_target_embedding
