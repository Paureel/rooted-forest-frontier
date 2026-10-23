import BothBadSideCover
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem tagged_colors_apart (A B C : List Nat) (ca cb cc : Nat→Nat)
 (apart : (∀x,x∈A→x∈B→False) ∧ (∀x,x∈A→x∈C→False) ∧ (∀x,x∈B→x∈C→False)) :
 (∀x,x∈A→∀y,y∈B→taggedColor A B ca cb cc x≠taggedColor A B ca cb cc y) ∧
 (∀x,x∈A→∀y,y∈C→taggedColor A B ca cb cc x≠taggedColor A B ca cb cc y) ∧
 (∀x,x∈B→∀y,y∈C→taggedColor A B ca cb cc x≠taggedColor A B ca cb cc y) := by
 constructor
 · intro x hx y hy
   have yn : y∉A:=fun h=>apart.1 y h hy
   simp only [taggedColor,ite_eq_left hx,ite_eq_right yn,ite_eq_left hy]
   omega
 · constructor
   · intro x hx y hy
     have ya : y∉A:=fun h=>apart.2.1 y h hy
     have yb : y∉B:=fun h=>apart.2.2 y h hy
     simp only [taggedColor,ite_eq_left hx,ite_eq_right ya,ite_eq_right yb]
     omega
   · intro x hx y hy
     have xa : x∉A:=fun h=>apart.1 x h hx
     have ya : y∉A:=fun h=>apart.2.1 y h hy
     have yb : y∉B:=fun h=>apart.2.2 y h hy
     simp only [taggedColor,ite_eq_right xa,ite_eq_left hx,ite_eq_right ya,ite_eq_right yb]
     omega

theorem tagged_partition_refines (S : Tree) (A B C : List Nat) (ca cb cc : Nat→Nat)
 (P : List (List Nat)) (nd : (leaves S).Nodup)
 (parents : partitionCheck (leaves S) [A,B,C]=true) (part : partitionCheck (leaves S) P=true)
 (mono : ∀K,K∈P→LabelMonochromatic (taggedColor A B ca cb cc) K) :
 VertexGeometry.Refines P [A,B,C] := by
 have apart:=tagged_colors_apart A B C ca cb cc (partition_parent_apart _ _ _ _ parents)
 have flat:=IndependentCommon.flatten_from_partition _ [A,B,C] nd parents
 have owner : ∀x,x∈leaves S→x∈A ∨ x∈B ∨ x∈C := by
  intro x hx
  have mem:=flat.mem_iff.mpr hx
  simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append] using mem
 intro K kP
 obtain ⟨x,xK⟩:=List.exists_mem_of_ne_nil K (partition_nonempty_member _ _ part K kP)
 have labels:=partition_member_labels _ _ part K kP
 rcases owner x (labels x xK) with xa|xb|xc
 · refine ⟨A,by simp,?_⟩
   intro y yK
   rcases owner y (labels y yK) with ya|yb|yc
   · exact ya
   · exact False.elim (apart.1 x xa y yb (mono K kP x y xK yK))
   · exact False.elim (apart.2.1 x xa y yc (mono K kP x y xK yK))
 · refine ⟨B,by simp,?_⟩
   intro y yK
   rcases owner y (labels y yK) with ya|yb|yc
   · exact False.elim (apart.1 y ya x xb (mono K kP y x yK xK))
   · exact yb
   · exact False.elim (apart.2.2 x xb y yc (mono K kP x y xK yK))
 · refine ⟨C,by simp,?_⟩
   intro y yK
   rcases owner y (labels y yK) with ya|yb|yc
   · exact False.elim (apart.2.1 y ya x xc (mono K kP y x yK xK))
   · exact False.elim (apart.2.2 y yb x xc (mono K kP y x yK xK))
   · exact yc

theorem tagged_output_refines (T S : Tree) (A B C : List Nat) (ca cb cc : Nat→Nat) (q : Nat)
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (o : Output) (member : o∈wholeOutputs S A B ca cb cc q) :
 VertexGeometry.Refines o.partition [A,B,C] := by
 exact tagged_partition_refines S A B C ca cb cc o.partition
  (IndependentReconstruction.proper_parts proper).2.1 parents
  (Assembly.generated_source_valid S (taggedColor A B ca cb cc) q o member).1
  (CutRealization.generate_monochromatic S (taggedColor A B ca cb cc) q o member)

theorem output_group_scope (T S : Tree) (A B C : List Nat) (P : List (List Nat))
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (part : partitionCheck (leaves S) P=true) (emb : pairwiseEmbeddings S P=true)
 (ref : VertexGeometry.Refines P [A,B,C]) :
 ForestState.proper (some T) (OutputState.sourceForest S P)=true ∧
 partitionCheck (ForestState.labels (some T)) [A++B,C]=true ∧ Owns (OutputState.sourceForest S P) [A++B,C] := by
 have pp:=IndependentReconstruction.proper_parts proper
 have mat:=OutputState.checked_materialization S P pp.2.1 part
 refine ⟨(FreshResidual.residual_transfer_scope.1 T S P [] proper part emb).2.1,?_,?_⟩
 · exact (partition_labels_congr (leaves S) (leaves T) _ (fun _=>pp.2.2.mem_iff.symm)).mp
    (ContactedHard2DP.merge_first_two_check _ _ _ _ parents)
 · intro s hs
   obtain ⟨D,dP,_,perm,_,_⟩:=mat.2.2 s hs
   obtain ⟨U,uParent,sub⟩:=ref D dP
   simp only [List.mem_cons,List.not_mem_nil,or_false] at uParent
   rcases uParent with eq|eq|eq <;>subst U
   · exact ⟨A++B,by simp,fun x hx=>List.mem_append_left _ (sub x (perm.mem_iff.mp hx))⟩
   · exact ⟨A++B,by simp,fun x hx=>List.mem_append_right _ (sub x (perm.mem_iff.mp hx))⟩
   · exact ⟨C,by simp,fun x hx=>sub x (perm.mem_iff.mp hx)⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.tagged_colors_apart
#print axioms ContactedHard2Survival.tagged_colors_apart
#check @ContactedHard2Survival.tagged_partition_refines
#print axioms ContactedHard2Survival.tagged_partition_refines
#check @ContactedHard2Survival.tagged_output_refines
#print axioms ContactedHard2Survival.tagged_output_refines
#check @ContactedHard2Survival.output_group_scope
#print axioms ContactedHard2Survival.output_group_scope
