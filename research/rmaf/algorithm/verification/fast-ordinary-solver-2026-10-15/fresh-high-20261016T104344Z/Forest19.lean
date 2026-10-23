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
  simp only [disjointVertices, List.all_eq_true, Bool.not_eq_true', List.contains_eq_false] at *
  intro v hv hv'
  exact h v hv' hv
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
#check List.nodup_iff_count_le_one
#check List.count_pos_iff
#check List.count_pos
#check List.count_le_one
#check List.count_eq_one_iff
#print axioms block_subset
#print axioms disjoint_pair
end OwnHigh
