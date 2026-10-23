import PartitionRefinement

namespace DegreeTwo
open RMAF

theorem partitionCheck_flatten_nodup (labels : List Nat) (bs : List (List Nat))
    (h : partitionCheck labels bs = true) : bs.flatten.Nodup := by
  obtain ⟨_,hc,hl⟩ := (partitionCheck_iff labels bs).mp h
  exact List.nodup_iff_count_of_mem.mpr (fun x hx => hc x (hl x hx))

theorem partitionCheck_block (labels : List Nat) (before after : List (List Nat))
    (B : List Nat) (h : partitionCheck labels (before ++ B :: after) = true) :
    B ≠ [] ∧ B.Nodup ∧ (∀ x, x ∈ B → x ∈ labels) := by
  obtain ⟨hn,_,hl⟩ := (partitionCheck_iff labels _).mp h
  have hf := partitionCheck_flatten_nodup labels _ h
  simp only [List.flatten_append, List.flatten_cons] at hf
  have hB := (List.nodup_append.mp (List.nodup_append.mp hf).2.1).1
  refine ⟨hn B (by simp),hB,?_⟩
  intro x hx
  exact hl x (List.mem_flatten.mpr ⟨B,by simp,hx⟩)

theorem agreement_block (t u : Tree) (before after : List (List Nat)) (B : List Nat)
    (h : agreement t u (before ++ B :: after) = true) :
    B ≠ [] ∧ B.Nodup ∧ (∀ x, x ∈ B → x ∈ leaves t) ∧
    (∀ x, x ∈ B → x ∈ leaves u) ∧ restrictionAgrees t u B = true := by
  simp only [agreement, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨ht,hu⟩,ha⟩,_⟩,_⟩ := h
  obtain ⟨hne,hn,hlt⟩ := partitionCheck_block (leaves t) before after B ht
  obtain ⟨_,_,hlu⟩ := partitionCheck_block (leaves u) before after B hu
  exact ⟨hne,hn,hlt,hlu,List.all_eq_true.mp ha B (by simp)⟩

end DegreeTwo
