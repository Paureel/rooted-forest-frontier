-- Own forest definition eliminators and only standard lemma type queries.
import Endpoint18
open RMAF Universal233
namespace OwnHigh
theorem block_subset (labels : List Nat) (F : List (List Nat))
    (h : partitionCheck labels F = true) (P : List Nat) (hp : P ∈ F) :
    ∀ x ∈ P, x ∈ labels := by
  simp only [partitionCheck, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem] at h
  intro x hx
  exact h.2 x (List.mem_flatten.mpr ⟨P,hp,hx⟩)
theorem disjoint_symm (V W : List Vertex) (h : disjointVertices V W = true) :
    disjointVertices W V = true := by
  simp only [disjointVertices, List.all_eq_true, Bool.not_eq_true', Bool.eq_false_iff, List.contains_iff_mem] at *
  intro v hv hv'
  exact h v (List.contains_iff_mem.mp hv') (List.contains_iff_mem.mpr hv)
theorem disjoint_pair (T : Tree) (F : List (List Nat)) (P Q : List Nat)
    (h : pairwiseEmbeddings T F = true) (hp : P ∈ F) (hq : Q ∈ F) (hne : P ≠ Q) :
    disjointVertices (minimalVertices P T) (minimalVertices Q T) = true := by
  induction F with
  | nil => simp at hp
  | cons R F ih =>
    simp only [pairwiseEmbeddings, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp hp with hp | hp
    · subst P
      rcases List.mem_cons.mp hq with hq | hq
      · exact False.elim (hne hq.symm)
      · exact h.1 Q hq
    · rcases List.mem_cons.mp hq with hq | hq
      · subst Q
        exact disjoint_symm _ _ (h.1 P hp)
      · exact ih h.2 hp hq
theorem partition_flat_nodup (labels : List Nat) (F : List (List Nat))
    (h : partitionCheck labels F = true) : F.flatten.Nodup := by
  simp only [partitionCheck, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem, beq_iff_eq] at h
  apply List.nodup_iff_count_of_mem.mpr
  intro x hx
  exact h.1.2 x (h.2 x hx)
theorem block_nodup (labels : List Nat) (F : List (List Nat))
    (h : partitionCheck labels F = true) (P : List Nat) (hp : P ∈ F) : P.Nodup := by
  exact (partition_flat_nodup labels F h).sublist (List.sublist_flatten_of_mem hp)
theorem label_block (labels : List Nat) (F : List (List Nat))
    (h : partitionCheck labels F = true) (a : Nat) (ha : a ∈ labels) : ∃ P ∈ F, a ∈ P := by
  simp only [partitionCheck, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem, beq_iff_eq] at h
  have hc : F.flatten.count a = 1 := h.1.2 a ha
  have hp : 0 < F.flatten.count a := by rw [hc]; decide
  exact List.mem_flatten.mp (List.count_pos_iff.mp hp)
#print axioms block_subset
#print axioms disjoint_pair
theorem other_of_not_singleton (P : List Nat) (a : Nat)
    (hn : P.Nodup) (ha : a ∈ P) (hs : P ≠ [a]) : ∃ x ∈ P, x ≠ a := by
  cases P with
  | nil => simp at ha
  | cons x xs =>
    by_cases he : x = a
    · subst x
      cases xs with
      | nil => exact False.elim (hs rfl)
      | cons y ys =>
        refine ⟨y, by simp, ?_⟩
        intro he
        exact (List.nodup_cons.mp hn).1 (by simp [he])
    · exact ⟨x, by simp, he⟩
end OwnHigh
