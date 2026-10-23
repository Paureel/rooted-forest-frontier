import GeneralPendantMergeR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

theorem refines_partition_perm {F P Q : List (List Nat)} (perm : P.Perm Q)
 (ref : VertexGeometry.Refines F P) : VertexGeometry.Refines F Q := by
 intro B hb
 obtain ⟨D,hd,sub⟩ := ref B hb
 exact ⟨D,perm.mem_iff.1 hd,sub⟩

theorem noncross_refines_literal (S : Tree) (C : List Vertex) (F : List (List Nat))
 (labels : ∀B∈F,∀x∈B,x∈leaves S)
 (no : ∀B∈F,∀p∈C,¬Crosses (subtreeLabels S p) B) :
 VertexGeometry.Refines F (Rule4.literalPartition S C) := by
 classical
 intro B hb
 by_cases hit : ∃p∈C,∃x∈B,x∈subtreeLabels S p
 · obtain ⟨p,hp,x,hx,xp⟩ := hit
   refine ⟨subtreeLabels S p,List.mem_append.2 (Or.inl (List.mem_map.2 ⟨p,hp,rfl⟩)),?_⟩
   intro y hy
   apply Classical.byContradiction
   intro yn
   exact no B hb p hp ⟨⟨x,hx,xp⟩,⟨y,hy,yn⟩⟩
 · refine ⟨(leaves S).filter (fun x=>C.all (fun p=>!(subtreeLabels S p).contains x)),List.mem_append.2 (Or.inr List.mem_cons_self),?_⟩
   intro x hx
   apply List.mem_filter.2
   refine ⟨labels B hb x hx,List.all_eq_true.2 ?_⟩
   intro p hp
   have absent : x∉subtreeLabels S p := fun xp=>hit ⟨p,hp,x,hx,xp⟩
   simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem] using absent

theorem cohabit_refines_address {T S : Tree} {q : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 {F : List (List Nat)} (hF : agreement T S F=true)
 (together : ∃B∈F,a∈B ∧ b∈B) : VertexGeometry.Refines F (Rule4.literalPartition S (cuts S a b)) := by
 obtain ⟨B,bF,ha,hb⟩ := together
 have old := hF
 simp only [agreement,Bool.and_eq_true] at old
 have labels := partition_labels old.1.1.1.2
 apply noncross_refines_literal S _ F labels
 intro C hC p cut cross
 obtain ⟨U,sub⟩ := vertex_has_subtree S p (List.mem_filter.1 cut).1
 have absent := cohabit_avoids_pendant proper ch cut sub hF bF ha hb
 have flags := (List.mem_filter.1 cut).2
 simp only [Bool.and_eq_true] at flags
 have pp := List.contains_iff_mem.1 flags.1.2
 have subAB : ∀x∈[a,b],x∈B := by
  intro x hx
  rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx : x=a∨x=b) with rfl|rfl
  · exact ha
  · exact hb
 have parentB := minimal_subset S subAB _ pp
 obtain ⟨⟨x,xC,xU⟩,⟨y,yC,yn⟩⟩ := cross
 rw [subtree_labels_lookup sub] at xU yn
 have parentC := crossing_boundary_in_minimal sub ⟨x,xU,xC⟩ ⟨y,labels C hC y yC,yC,yn⟩
 have eq := shared_hull_block_equal old.2 bF hC parentB parentC
 exact absent x (eq ▸ xC) xU

theorem cohabit_refines_all {T S : Tree} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : HasCherry a b T)
 {F : List (List Nat)} (hF : agreement T S F=true)
 (together : ∃B∈F,a∈B ∧ b∈B) : VertexGeometry.Refines F (Rule4.literalPartition S (cuts S a b)) := by
 obtain ⟨q,hq⟩ := cherry_address_own ch
 rcases hq with forward|reverse
 · exact cohabit_refines_address proper forward hF together
 · have swapped := cohabit_refines_address proper reverse hF (by
    obtain ⟨B,hB,ha,hb⟩ := together;exact ⟨B,hB,hb,ha⟩)
   rw [←cuts_swap_own S a b] at swapped
   exact swapped

theorem endpoint_cases_all {T S : Tree} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : HasCherry a b T)
 {F : List (List Nat)} (hF : agreement T S F=true) :
 [a]∈F ∨ [b]∈F ∨ ∃B∈F,a∈B ∧ b∈B := by
 obtain ⟨q,hq⟩ := cherry_address_own ch
 rcases hq with forward|reverse
 · exact endpoint_partition_cases proper forward hF
 · rcases endpoint_partition_cases proper reverse hF with hb|ha|both
   · exact Or.inr (Or.inl hb)
   · exact Or.inl ha
   · obtain ⟨B,hB,hb,ha⟩ := both;exact Or.inr (Or.inr ⟨B,hB,ha,hb⟩)

theorem proper_swap_own {T S : Tree} (proper : DepthOne.proper T S=true) : DepthOne.proper S T=true := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
 simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using And.intro ns (And.intro nt perm.symm)

theorem singleton_block_eq {T S : Tree} {F : List (List Nat)} (proper : DepthOne.proper T S=true)
 (hF : agreement T S F=true) {B : List Nat} {a : Nat} (aF : [a]∈F) (bF : B∈F) (ha : a∈B) : B=[a] := by
 have checks := hF
 simp only [agreement,Bool.and_eq_true] at checks
 have nd := (IndependentCommon.flatten_from_partition _ F (IndependentReconstruction.proper_parts proper).1 checks.1.1.1.1).symm.nodup (IndependentReconstruction.proper_parts proper).1
 exact IndependentPaid.shared_block_equal nd bF aF ha List.mem_cons_self

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.refines_partition_perm
#print axioms ContactedForward.refines_partition_perm
#check @ContactedForward.noncross_refines_literal
#print axioms ContactedForward.noncross_refines_literal
#check @ContactedForward.cohabit_refines_address
#print axioms ContactedForward.cohabit_refines_address
#check @ContactedForward.cohabit_refines_all
#print axioms ContactedForward.cohabit_refines_all
#check @ContactedForward.endpoint_cases_all
#print axioms ContactedForward.endpoint_cases_all
#check @ContactedForward.proper_swap_own
#print axioms ContactedForward.proper_swap_own
#check @ContactedForward.singleton_block_eq
#print axioms ContactedForward.singleton_block_eq
