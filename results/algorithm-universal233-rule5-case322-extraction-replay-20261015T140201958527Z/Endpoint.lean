import SourceBridge
import Executable

namespace Universal233.HardParent
open RMAF CoreGraph Integration VertexGeometry

theorem block_labels {T : Tree} {F : List (List Nat)}
    (hp : partitionCheck (leaves T) F = true) {B : List Nat} (hB : B ∈ F)
    {x : Nat} (hx : x ∈ B) : x ∈ leaves T := by
  have hall : F.flatten.all (fun y => (leaves T).contains y) = true := by
    simp only [partitionCheck, Bool.and_eq_true] at hp
    exact hp.2
  exact List.contains_iff_mem.1 ((List.all_eq_true.1 hall) x (List.mem_flatten.2 ⟨B,hB,hx⟩))

theorem block_count_le_one {T : Tree} {F : List (List Nat)}
    (hp : partitionCheck (leaves T) F = true) {B : List Nat} (hB : B ∈ F)
    {x : Nat} (hx : x ∈ B) : B.count x ≤ 1 := by
  have hc : (leaves T).all (fun y => F.flatten.count y == 1) = true := by
    simp only [partitionCheck, Bool.and_eq_true] at hp
    exact hp.1.2
  have he : F.flatten.count x = 1 :=
    beq_iff_eq.1 ((List.all_eq_true.1 hc) x (block_labels hp hB hx))
  have hle := (List.sublist_flatten_of_mem hB).count_le x
  omega

theorem block_singleton_of_only {T : Tree} {F : List (List Nat)}
    (hp : partitionCheck (leaves T) F = true) {B : List Nat} (hB : B ∈ F)
    {x : Nat} (hx : x ∈ B) (only : ∀ y, y ∈ B → y = x) : B = [x] := by
  cases B with
  | nil => simp at hx
  | cons y ys =>
    have hy := only y (by simp)
    subst y
    have hc := block_count_le_one hp hB (by simp : x ∈ x :: ys)
    have hn : x ∉ ys := by
      intro hm
      have hs : 0 < ys.count x := List.count_pos_iff.2 hm
      simp only [List.count_cons_self] at hc
      omega
    have he : ys = [] := by
      cases ys with
      | nil => rfl
      | cons z zs =>
        have hz := only z (by simp)
        subst z
        simp at hn
    simp [he]

theorem checked_singleton_is_literal {T : Tree} {F : List (List Nat)}
    (hp : partitionCheck (leaves T) F = true)
    (he : pairwiseEmbeddings T F = true) {u : RMAF.Vertex} {x : Nat}
    (hu : LeafAt T u x) (hs : SingletonBlock (checkedSourcePartition T F hp he) u) :
    [x] ∈ F := by
  obtain ⟨B,hB,hx⟩ := partitionCheck_covers _ F hp x (leafAt_label T u x hu)
  have only : ∀ y, y ∈ B → y = x := by
    intro y hy
    obtain ⟨v,hv⟩ := (singleton_selected_exists T y).2 (block_labels hp hB hy)
    have hv' : LeafAt T v y := (leafAt_selected T v y).2 hv
    have ho := (checkedSourcePartition_owner T F hp he v u y x hv' hu).2 ⟨B,hB,hy,hx⟩
    have heq := hs v y hv' ho
    subst v
    unfold LeafAt at hv' hu
    rw [hu] at hv'
    exact Tree.leaf.inj (Option.some.inj hv').symm
  simpa [block_singleton_of_only hp hB hx only] using hB

/-- The singleton cases are proved against the ORIGINAL agreement partition.
No history, owner assignment, or reachability field is supplied by the caller. -/
theorem actual_cherry_endpoint_alternative {T S : Tree} {F : List (List Nat)}
    (ha : agreement T S F = true) {p : RMAF.Vertex} {a b : Nat}
    (hc : CherryAt T p a b) :
    [a] ∈ F ∨ [b] ∈ F ∨ ∃ B, B ∈ F ∧ a ∈ B ∧ b ∈ B := by
  have hp : partitionCheck (leaves T) F = true := by
    simp only [agreement, Bool.and_eq_true] at ha
    exact ha.1.1.1.1
  have he : pairwiseEmbeddings T F = true := by
    simp only [agreement, Bool.and_eq_true] at ha
    exact ha.1.2
  let P := checkedSourcePartition T F hp he
  by_cases hl : SingletonBlock P (p ++ [false])
  · exact Or.inl (checked_singleton_is_literal hp he (cherry_left hc) hl)
  · by_cases hr : SingletonBlock P (p ++ [true])
    · exact Or.inr (Or.inl (checked_singleton_is_literal hp he (cherry_right hc) hr))
    · have hpl := nonsingleton_parent P (cherry_left hc) hl
      have hpr := nonsingleton_parent P (cherry_right hc) hr
      have ho := P.disjoint _ _ _ hpl hpr
      exact Or.inr (Or.inr ((checkedSourcePartition_owner T F hp he _ _ _ _
        (cherry_left hc) (cherry_right hc)).1 ho))
end Universal233.HardParent
