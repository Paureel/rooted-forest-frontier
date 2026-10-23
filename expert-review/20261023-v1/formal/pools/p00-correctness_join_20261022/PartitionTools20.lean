-- Own list partition facts, using standard list facts only.
import BranchGeometry34
open RMAF Universal233 CherryBranching VertexGeometry OwnHigh
namespace HighChildren
theorem partition_from_flat (labels : List Nat) (F : List (List Nat))
    (hn : F.flatten.Nodup) (hne : ∀ P∈F,P≠[])
    (heq : ∀x,x∈F.flatten ↔ x∈labels) : partitionCheck labels F=true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro P hp
    have h := hne P hp
    cases P with
    | nil => exact False.elim (h rfl)
    | cons x xs => rfl
  · intro x hx
    have hc := List.nodup_iff_count_of_mem.mp hn x ((heq x).mpr hx)
    exact beq_iff_eq.mpr hc
  · intro x hx
    exact List.contains_iff_mem.mpr ((heq x).mp hx)
theorem singleton_partition (S : Tree) (a b : Nat)
    (hn : (leaves S).Nodup) (ha : a∈leaves S) (hb : b∈leaves S) (hab : a≠b) :
    partitionCheck (leaves S) (singletonPartition S a)=true := by
  have hflat : (singletonPartition S a).flatten=[a]++(leaves S).filter (fun x => x != a) := by
    simp only [singletonPartition,List.flatten_cons,List.flatten_nil,List.append_nil]
  have hnod : ((leaves S).filter (fun x => x != a)).Nodup := hn.filter _
  have hna : a∉(leaves S).filter (fun x => x != a) := by
    intro h
    have hne := (List.mem_filter.mp h).2
    simp only [bne_self_eq_false] at hne
    cases hne
  apply partition_from_flat
  · rw [hflat]
    exact List.nodup_cons.mpr ⟨hna,hnod⟩
  · intro P hp
    simp only [singletonPartition,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact List.cons_ne_nil _ _
    · intro hnil
      have hmem : b∈(leaves S).filter (fun x => x != a) := List.mem_filter.mpr ⟨hb,by simpa only [bne_iff_ne] using hab.symm⟩
      rw [hnil] at hmem
      exact List.not_mem_nil hmem
  · intro x
    rw [hflat]
    simp only [List.mem_append,List.mem_singleton,List.mem_filter,bne_iff_ne]
    constructor
    · rintro (rfl | ⟨hx,_⟩)
      · exact ha
      · exact hx
    · intro hx
      by_cases he : x=a
      · exact Or.inl he
      · exact Or.inr ⟨hx,he⟩
end HighChildren
