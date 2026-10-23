import LiteralValidity
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Overlap

theorem partition_disjoint (L : List Nat) (P : List (List Nat)) (part : partitionCheck L P=true)
 (A B : List Nat) (aP : A∈P) (bP : B∈P) (ne : A≠B) : ∀x,x∈A→x∈B→False := by
 intro x ha hb
 exact ne (ForestGroups.group_unique L P part A B aP bP x ha hb)

theorem three_parent_ne (L A B C : List Nat) (part : partitionCheck L [A,B,C]=true) : A≠B ∧ A≠C ∧ B≠C := by
 have nd:=checked_family_nodup L _ part
 refine ⟨?_,?_,?_⟩
 · intro eq
   exact (List.nodup_cons.mp nd).1 (by rw [eq];exact List.mem_cons_self)
 · intro eq
   exact (List.nodup_cons.mp nd).1 (by rw [eq];exact List.mem_cons_of_mem _ List.mem_cons_self)
 · simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1

theorem overlap_not_target_leaf (T : Tree) (A B : List Nat) (v : RMAF.Vertex)
 (apart : ∀x,x∈A→x∈B→False) (a : v∈minimalVertices A T) (b : v∈minimalVertices B T) :
 ¬selectedLeaves (leaves T) T v := by
 have no:=(disjoint_parent_overlap_nonlabel A B T v apart a b).1
 intro leaf
 have reach : Reach (selectedLeaves A T) v := hull_subset_reach _ _ ((minimalVertices_correct A T v).mp a)
 exact no (selected_leaf_reach_implies_self (leaves T) A T v leaf reach)

theorem actual_chain_guards (T S : Tree) (A B C : List Nat) (v w : RMAF.Vertex)
 (part : partitionCheck (leaves S) [A,B,C]=true)
 (hab : overlap T A B=some v) (hbc : overlap T B C=some w) (hac : overlap T A C=none) :
 ChainGuards T A B C v w := by
 have ne:=three_parent_ne _ _ _ _ part
 have ab:=repeated_common_some _ _ v hab
 have bc:=repeated_common_some _ _ w hbc
 have clear:=overlap_none_clear T A C hac
 have dab:=partition_disjoint _ _ part A B List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) ne.1
 have dbc:=partition_disjoint _ _ part B C (List.mem_cons_of_mem _ List.mem_cons_self)
  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ne.2.2
 have vn:=overlap_not_target_leaf T A B v dab ab.1 ab.2
 have wn:=overlap_not_target_leaf T B C w dbc bc.1 bc.2
 have diff : v≠w := by intro eq;have wc:=bc.2;rw [←eq] at wc;exact clear v ab.1 wc
 exact ⟨vn,wn,ab.1,ab.2,bc.1,bc.2,clear,diff⟩
end ContactedHard2Overlap

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Overlap.partition_disjoint
#print axioms ContactedHard2Overlap.partition_disjoint
#check @ContactedHard2Overlap.three_parent_ne
#print axioms ContactedHard2Overlap.three_parent_ne
#check @ContactedHard2Overlap.overlap_not_target_leaf
#print axioms ContactedHard2Overlap.overlap_not_target_leaf
#check @ContactedHard2Overlap.actual_chain_guards
#print axioms ContactedHard2Overlap.actual_chain_guards
