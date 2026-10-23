/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- An independent exchange building block from own frozen common geometry. -/
import SlimCoarsenGeometryV5R2
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentOneExchange

def mergeCommon (a b z : Nat) (F : List (List Nat)) :=
 (IndependentGeometry.coarsen a b z F).map (expandBlock a b z)

theorem filter_nil_strict (L : List (List Nat)) (h : []∈L) :
 (L.filter (fun B=>!B.isEmpty)).length+1≤L.length := by
 induction L with
 | nil => simp at h
 | cons B rest ih =>
  cases B with
  | nil =>
   have le := List.length_filter_le (fun B : List Nat=>!B.isEmpty) rest
   simpa using Nat.add_le_add_right le 1
  | cons x xs =>
   have tail : []∈rest := by simpa using h
   have bound := ih tail
   simpa using Nat.add_le_add_right bound 1

theorem common_singleton_merge {a b z : Nat} {T S : Tree}
 (ht : HasCherry a b T) (hs : HasCherry a b S)
 (proper : DepthOne.proper T S=true) (fresh : z∉leaves T)
 (F : List (List Nat)) (hF : agreement T S F=true) (singleton : [b]∈F) :
 agreement T S (mergeCommon a b z F)=true ∧
 (mergeCommon a b z F).length+1≤F.length ∧
 ∃B∈mergeCommon a b z F,a∈B ∧ b∈B := by
 have coarsened := IndependentGeometry.common_coarsening ht hs proper fresh F hF
 have expanded := IndependentGeometry.common_expansion ht hs proper fresh
  (IndependentGeometry.coarsen a b z F) coarsened.1
 have empty : []∈F.map (IndependentGeometry.shrinkBlock a b z) := by
  apply List.mem_map.2
  exact ⟨[b],singleton,by simp [IndependentGeometry.shrinkBlock]⟩
 have less := filter_nil_strict _ empty
 have size : (mergeCommon a b z F).length+1≤F.length := by
  simpa only [mergeCommon,List.length_map,IndependentGeometry.coarsen,List.length_map] using less
 obtain ⟨nt,_,_⟩ := IndependentReconstruction.proper_parts proper
 obtain ⟨rest,_,normal⟩ := IndependentCommon.contraction_normal ht z nt
 have zlabel : z∈leaves (contract a b z T) := normal.mem_iff.2 (by simp)
 have partition := coarsened.1
 simp only [agreement,Bool.and_eq_true] at partition
 have covered := IndependentReconstruction.coverage _ _ partition.1.1.1.1 zlabel
 obtain ⟨B,hB,zB⟩ := List.mem_flatten.1 covered
 refine ⟨expanded,size,expandBlock a b z B,List.mem_map.2 ⟨B,hB,rfl⟩,?_,?_⟩
 · exact (IndependentGeometry.expand_membership B a b z a).2 (Or.inr ⟨zB,Or.inl rfl⟩)
 · exact (IndependentGeometry.expand_membership B a b z b).2 (Or.inr ⟨zB,Or.inr rfl⟩)

/- Hence a minimum common-cherry forest cannot isolate either endpoint. -/
theorem minimum_common_no_singleton {a b z : Nat} {T S : Tree}
 (ht : HasCherry a b T) (hs : HasCherry a b S)
 (proper : DepthOne.proper T S=true) (fresh : z∉leaves T)
 (F : List (List Nat)) (hF : agreement T S F=true)
 (least : ∀G,agreement T S G=true→F.length≤G.length) : [b]∉F := by
 intro singleton
 obtain ⟨valid,size,_⟩ := common_singleton_merge ht hs proper fresh F hF singleton
 have low := least _ valid
 omega
end IndependentOneExchange

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @IndependentOneExchange.filter_nil_strict
#print axioms IndependentOneExchange.filter_nil_strict
#check @IndependentOneExchange.common_singleton_merge
#print axioms IndependentOneExchange.common_singleton_merge
#check @IndependentOneExchange.minimum_common_no_singleton
#print axioms IndependentOneExchange.minimum_common_no_singleton
