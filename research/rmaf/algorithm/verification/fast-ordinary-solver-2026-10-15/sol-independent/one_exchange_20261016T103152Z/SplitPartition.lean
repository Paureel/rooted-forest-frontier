/- Binary splitting preserves exact label partitions and original refinement. -/
import SingleBoundaryCountV3
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentOneExchange

theorem append_cons_move (L R : List Nat) (x : Nat) :
 (L++x::R).Perm (x::(L++R)) := by
 induction L with
 | nil => exact .refl _
 | cons y rest ih => exact (List.Perm.cons y ih).trans (List.Perm.swap x y _)

theorem complement_filters_perm (X B : List Nat) :
 ((B.filter X.contains)++B.filter (fun x=>!X.contains x)).Perm B := by
 induction B with
 | nil => exact .refl _
 | cons x rest ih =>
  cases h : X.contains x with
  | false =>
   simp only [List.filter_cons,h,Bool.false_eq_true,ite_false,Bool.not_false,ite_true]
   exact (append_cons_move _ _ x).trans (List.Perm.cons x ih)
  | true =>
   simp only [List.filter_cons,h,ite_true,Bool.not_true,Bool.false_eq_true,ite_false,List.cons_append]
   exact List.Perm.cons x ih

theorem split_block_flatten (X B : List Nat) : (splitBlock X B).flatten.Perm B := by
 rw [splitBlock,IndependentGeometry.nonempty_flatten]
 simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using complement_filters_perm X B

theorem split_forest_flatten (X : List Nat) (F : List (List Nat)) :
 (splitForest X F).flatten.Perm F.flatten := by
 induction F with
 | nil => exact .refl _
 | cons B rest ih =>
  change ((splitBlock X B)++splitForest X rest).flatten.Perm (B++rest.flatten)
  rw [List.flatten_append]
  exact (split_block_flatten X B).append ih

theorem split_nonempty (X : List Nat) (F : List (List Nat)) : ∀B∈splitForest X F,B≠[] := by
 intro B hB
 obtain ⟨C,hC,hB⟩ := List.mem_flatMap.1 hB
 have check := (List.mem_filter.1 hB).2
 intro empty
 simp [empty] at check

theorem split_partition (L X : List Nat) (F : List (List Nat))
 (nd : L.Nodup) (part : partitionCheck L F=true) : partitionCheck L (splitForest X F)=true := by
 have original := IndependentCommon.flatten_from_partition L F nd part
 exact IndependentCommon.partition_from_flatten L _ nd (split_nonempty X F)
  ((split_forest_flatten X F).trans original)

theorem split_refines_binary (L X : List Nat) (F : List (List Nat))
 (part : partitionCheck L F=true) :
 VertexGeometry.Refines (splitForest X F) [X,L.filter (fun x=>!X.contains x)] := by
 have labels : ∀B∈F,∀x∈B,x∈L := by
  have pp := part
  simp only [partitionCheck,Bool.and_eq_true] at pp
  intro B hB x hx
  exact List.contains_iff_mem.1 (List.all_eq_true.1 pp.2 x (List.mem_flatten.2 ⟨B,hB,hx⟩))
 intro B hB
 obtain ⟨C,hC,hB⟩ := List.mem_flatMap.1 hB
 have member := (List.mem_filter.1 hB).1
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with eq|eq
 · subst B
   refine ⟨X,by simp,?_⟩
   intro x hx
   exact List.contains_iff_mem.1 (List.mem_filter.1 hx).2
 · subst B
   refine ⟨L.filter (fun x=>!X.contains x),by simp,?_⟩
   intro x hx
   have p := List.mem_filter.1 hx
   exact List.mem_filter.2 ⟨labels C hC x p.1,p.2⟩

theorem original_split_label_count {T S U : Tree} {p : Vertex} {F : List (List Nat)}
 (proper : DepthOne.proper T S=true) (sub : CoreGraph.subtree S p=some U)
 (hF : agreement T S F=true) :
 partitionCheck (leaves T) (splitForest (leaves U) F)=true ∧
 partitionCheck (leaves S) (splitForest (leaves U) F)=true ∧
 VertexGeometry.Refines (splitForest (leaves U) F)
  [leaves U,(leaves S).filter (fun x=>!(leaves U).contains x)] ∧
 (splitForest (leaves U) F).length≤F.length+1 := by
 obtain ⟨nt,ns,_⟩ := IndependentReconstruction.proper_parts proper
 have checks := hF
 simp only [agreement,Bool.and_eq_true] at checks
 exact ⟨split_partition _ _ F nt checks.1.1.1.1,split_partition _ _ F ns checks.1.1.1.2,
  split_refines_binary _ _ F checks.1.1.1.2,original_split_count sub ns hF⟩
end IndependentOneExchange
