-- Literal original child fields and generic component-count consequences.
import BranchGeometry34
open RMAF Universal233 CherryBranching VertexGeometry OwnHigh
namespace HighChildren
theorem literal_fields (S : Tree) (a b : Nat) (c : Child) (hc : c∈branches S a b) :
    c.sourceForest=c.partition.filterMap (fun B => restrict B S) ∧
    c.partition.length=c.paid+1 ∧
    (c=singletonChild S a ∨ c=singletonChild S b ∨ c=pendantChild S a b) := by
  simp only [branches,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨rfl,rfl,Or.inl rfl⟩
  · exact ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩
  · refine ⟨rfl,?_,Or.inr (Or.inr rfl)⟩
    simp only [pendantChild,makeChild,pendantPartition,List.length_append,List.length_map,List.length_singleton]
theorem positive_paid (S : Tree) (a b : Nat) (hh : 3≤(cuts S a b).length)
    (c : Child) (hc : c∈branches S a b) : 0<c.paid := by
  rcases (literal_fields S a b c hc).2.2 with rfl | rfl | rfl
  · exact Nat.zero_lt_one
  · exact Nat.zero_lt_one
  · exact Nat.lt_of_lt_of_le (by decide : 0<3) hh
theorem restrictions_exist (S : Tree) (F : List (List Nat))
    (hp : partitionCheck (leaves S) F=true) :
    ∀ B∈F, ∃ U, restrict B S=some U := by
  intro B hb
  have hn : B≠[] := by
    have h:=hp
    simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true,Bool.not_eq_true'] at h
    have he : B.isEmpty=false := h.1.1 B hb
    intro hn
    subst B
    cases he
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B hn
  exact RestrictionBridge.restriction_exists S B ⟨x,block_subset (leaves S) F hp B hb x hx,hx⟩
theorem filterMap_full_length (S : Tree) (F : List (List Nat))
    (h : ∀ B∈F, ∃ U, restrict B S=some U) :
    (F.filterMap (fun B => restrict B S)).length=F.length := by
  induction F with
  | nil => rfl
  | cons B F ih =>
    obtain ⟨U,hU⟩ := h B (List.mem_cons_self)
    have ht : ∀ C∈F, ∃ V, restrict C S=some V := fun C hc => h C (List.mem_cons_of_mem B hc)
    simpa only [List.filterMap_cons,hU,List.length_cons] using congrArg Nat.succ (ih ht)
theorem source_component_count (S : Tree) (a b : Nat) (c : Child)
    (hc : c∈branches S a b) (hp : partitionCheck (leaves S) c.partition=true) :
    c.sourceForest.length=c.paid+1 := by
  have hf:=literal_fields S a b c hc
  rw [hf.1,filterMap_full_length S c.partition (restrictions_exist S c.partition hp),hf.2.1]
theorem component_labels (S : Tree) (P : List Nat) (U : Tree)
    (hr : restrict P S=some U) (hp : ∀x∈P,x∈leaves S) :
    ∀x,x∈leaves U ↔ x∈P := by
  intro x
  rw [RestrictionBridge.restricted_labels_exact S U P hr]
  exact ⟨And.right,fun hx => ⟨hp x hx,hx⟩⟩
end HighChildren
