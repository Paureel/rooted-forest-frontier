import ParentCollapseScope
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Survival

theorem good_edge_collapse (T S : Tree) (A B C : List Nat) (p : RMAF.Vertex) (H : List (List Nat))
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (sourceEmb : pairwiseEmbeddings S [A,B,C]=true)
 (agree : agreement T S H=true) (ref : VertexGeometry.Refines H [A,B,C])
 (clearAC : ContactedHard2Overlap.Clear T A C) (clearEdge : PairGeometry.ActualClear T A B p)
 (mono : ∀K,K∈H→LabelMonochromatic (sideColor (PairGeometry.descendants T p)) K)
 (good : restrictionAgrees S T A=true) (two : 2≤(family A H).length) :
 agreement T S (collapseParent A H)=true ∧
 VertexGeometry.Refines (collapseParent A H) [A,B,C] ∧
 (collapseParent A H).length+1≤H.length ∧
 ParentMono (collapseParent A H) B (sideColor (PairGeometry.descendants T p)) := by
 have an:=partition_nonempty_member _ _ part A (by simp)
 have ne:=agreement_nonempty T S H agree
 have parentApart:=partition_parent_apart _ _ _ _ part
 have targetClear : ∀K,K∈outsideParent A H→disjointVertices (minimalVertices A T) (minimalVertices K T)=true := by
  intro K member
  have kh:=(List.mem_filter.mp member).1
  rcases outside_parent_owner A B C H ref K member with kb|kc
  · obtain ⟨inside,sub⟩:=side_monochrome_in_region T B K p (ne K kh) kb (mono K kh)
    apply List.all_eq_true.mpr
    intro v va
    have no : v∉minimalVertices K T := by
     intro vk
     exact clearEdge.2 inside v (ContactedClade.minimal_subset T (fun _ hx=>sub hx) v vk) va
    simpa using no
  · apply List.all_eq_true.mpr
    intro v va
    have no : v∉minimalVertices K T := fun vk=>clearAC v va (ContactedClade.minimal_subset T (fun _ hx=>kc hx) v vk)
    simpa using no
 have checks:=sourceEmb
 simp only [pairwiseEmbeddings,Bool.and_eq_true] at checks
 have sourceClear : ∀K,K∈outsideParent A H→disjointVertices (minimalVertices A S) (minimalVertices K S)=true := by
  intro K member
  rcases outside_parent_owner A B C H ref K member with kb|kc
  · exact ContactedClade.disjoint_subsets S (fun _ hx=>hx) (fun _ hx=>kb hx) (List.all_eq_true.mp checks.1 B (by simp))
  · exact ContactedClade.disjoint_subsets S (fun _ hx=>hx) (fun _ hx=>kc hx) (List.all_eq_true.mp checks.1 C (by simp))
 have global:=collapse_agreement T S A H proper agree an (ContactedHard2DP.restriction_good_swap good)
  (parent_family_perm T S A B C H proper part agree ref) targetClear sourceClear
 refine ⟨global,collapse_refines A B C H ref,collapse_count A H two,?_⟩
 intro K member subB
 rcases List.mem_cons.mp member with eq|rest
 · subst K
   obtain ⟨x,xA⟩:=List.exists_mem_of_ne_nil A an
   exact False.elim (parentApart.1 x xA (subB xA))
 · exact mono K (List.mem_filter.mp rest).1
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.good_edge_collapse
#print axioms ContactedHard2Survival.good_edge_collapse
