import Singleton

namespace ForestState
open RMAF RestrictionBridge

theorem singleton_leaves_iff (s : Tree) (a : Nat) : leaves s = [a] ↔ s = .leaf a := by
  exact ⟨tree_of_singleton_leaves s a,fun h => by subst s; rfl⟩

theorem map_cleanup_sources (ss : List Tree) (a : Nat) :
    (cleanupSources ss a).map leaves = (ss.map leaves).erase [a] := by
  have hp : (fun s : Tree => leaves s == [a]) = (fun s => s == .leaf a) := by
    funext s
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq,singleton_leaves_iff]
  simp only [cleanupSources,List.erase_eq_eraseP',List.eraseP_map,Function.comp_def,hp]

theorem flatten_count_erase (F : List (List Nat)) (B : List Nat) (hB : B ∈ F) (x : Nat) :
    (F.erase B).flatten.count x + B.count x = F.flatten.count x := by
  induction F with
  | nil => simp at hB
  | cons C F ih =>
    by_cases he : C = B
    · subst C
      simp [List.count_append,Nat.add_comm]
    · have hb : B ∈ F := by simpa [Ne.symm he] using hB
      have hi := ih hb
      have hbe : (C == B) = false := by simpa only [beq_eq_false_iff_ne] using he
      simp only [List.erase_cons_tail (a := B) (b := C) (l := F) (by simp [hbe]),List.flatten_cons,List.count_append]
      omega

theorem partition_remove_singleton (L : List Nat) (F : List (List Nat)) (a : Nat)
    (hp : partitionCheck L F = true) (nd : L.Nodup) (ha : [a] ∈ F) :
    partitionCheck (L.erase a) (F.erase [a]) = true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    have hn := checked_nonempty L F hp B (List.mem_of_mem_erase hB)
    simpa using hn
  · intro x hx
    have hxl := List.mem_of_mem_erase hx
    have hxa := (nd.mem_erase_iff.1 hx).1
    have hc := flatten_count_erase F [a] ha x
    have ho := checked_count L F hp hxl
    have hz : ([a] : List Nat).count x = 0 := by simp [hxa,Ne.symm hxa]
    apply beq_iff_eq.2
    omega
  · intro x hx
    obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 hx
    have hxl := checked_label L F hp (List.mem_of_mem_erase hB) hxB
    have hxa : x ≠ a := by
      intro he
      subst x
      have hc := flatten_count_erase F [a] ha a
      have ho := checked_count L F hp hxl
      have hm : a ∈ (F.erase [a]).flatten := List.mem_flatten.2 ⟨B,hB,hxB⟩
      have hpos := List.count_pos_iff.2 hm
      simp at hc
      omega
    exact List.contains_iff_mem.2 (nd.mem_erase_iff.2 ⟨hxa,hxl⟩)

theorem cleanup_labels (T : Option Tree) (a : Nat) (nd : (labels T).Nodup) :
    labels (cleanupTarget T a) = (labels T).erase a := by
  cases T with
  | none => rfl
  | some t =>
    change optionLeaves (restrict ((leaves t).erase a) t) = (leaves t).erase a
    rw [restrict_leaves]
    have he : (leaves t).filter (fun x => ((leaves t).erase a).contains x) =
        (leaves t).filter (fun x => x != a) := by
      apply List.filter_congr
      intro x hx
      apply Bool.eq_iff_iff.2
      simp only [List.contains_iff_mem,bne_iff_ne]
      exact ⟨fun h => (nd.mem_erase_iff.1 h).1,fun h => nd.mem_erase_iff.2 ⟨h,hx⟩⟩
    rw [he]
    exact (nd.erase_eq_filter a).symm

theorem singleton_strict_decrease (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (a : Nat) (h : agrees T ss F = true) (ha : .leaf a ∈ ss) :
    (labels (cleanupTarget T a)).length + 1 = (labels T).length := by
  have hp := (agrees_parts T ss F h).1
  have hm := (singleton_source_owner T ss a hp ha).1
  rw [cleanup_labels T a (proper_parts T ss hp).1,List.length_erase_of_mem hm]
  have hn := List.length_pos_iff.2 (List.ne_nil_of_mem hm)
  omega

theorem cleanup_proper (T : Option Tree) (ss : List Tree) (a : Nat)
    (hp : proper T ss = true) (ha : .leaf a ∈ ss) :
    proper (cleanupTarget T a) (cleanupSources ss a) = true := by
  obtain ⟨nd,hQ⟩ := proper_parts T ss hp
  have hm : [a] ∈ ss.map leaves := List.mem_map.2 ⟨.leaf a,ha,rfl⟩
  have he := partition_remove_singleton (labels T) (ss.map leaves) a hQ nd hm
  simp only [proper,Bool.and_eq_true,decide_eq_true_eq]
  rw [cleanup_labels T a nd,map_cleanup_sources]
  exact ⟨nd.erase a,he⟩

end ForestState
