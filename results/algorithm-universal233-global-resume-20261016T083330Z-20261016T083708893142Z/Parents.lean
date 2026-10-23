import Count
namespace BinaryExchange
open RMAF VertexGeometry

def Refines (F P : List (List Nat)) : Prop := ∀ C, C ∈ F → ∃ E, E ∈ P ∧ Sub C E

def inside (C A : List Nat) : Bool := C.all (A.contains ·)

theorem inside_iff (C A : List Nat) : inside C A = true ↔ Sub C A := by
  simp only [inside,List.all_eq_true,List.contains_iff_mem,Sub]

def aParts (A : List Nat) (F : List (List Nat)) := F.filter (inside · A)
def residual (A : List Nat) (F : List (List Nat)) := F.filter (fun C => !inside C A)
def bParts (A B : List Nat) (F : List (List Nat)) := (residual A F).filter (inside · B)
def outside (A B : List Nat) (F : List (List Nat)) := (residual A F).filter (fun C => !inside C B)

theorem grouped_perm (A B : List Nat) (F : List (List Nat)) :
    (aParts A F ++ bParts A B F ++ outside A B F).Perm F := by
  have h₁ := List.filter_append_perm (inside · A) F
  have h₂ := List.filter_append_perm (inside · B) (residual A F)
  simpa only [bParts,outside,List.append_assoc] using
    (List.Perm.append_left (aParts A F) h₂).trans (by simpa [aParts,residual] using h₁)

theorem partition_perm (L : List Nat) (F G : List (List Nat))
    (h : F.Perm G) (hp : partitionCheck L F = true) : partitionCheck L G = true := by
  obtain ⟨hn,hc,hl⟩ := partition_parts L F hp
  apply partition_intro
  · intro C hC; exact hn C (h.mem_iff.2 hC)
  · intro x hx; rw [← h.flatten.count_eq x]; exact hc x hx
  · intro x hx; exact hl x (h.flatten.mem_iff.2 hx)

theorem agreement_perm (s t : Tree) (F G : List (List Nat))
    (h : F.Perm G) (ha : agreement s t F = true) : agreement s t G = true := by
  obtain ⟨hps,hpt,hs,hds,hdt⟩ := agreement_parts s t F ha
  unfold agreement
  simp only [Bool.and_eq_true,List.all_eq_true,executable_pairwiseEmbeddings]
  exact ⟨⟨⟨⟨partition_perm (leaves s) F G h hps,partition_perm (leaves t) F G h hpt⟩,
    by intro C hC; exact hs C (h.mem_iff.2 hC)⟩,
    (h.pairwise_iff (fun h => disj_symm h)).1 hds⟩,
    (h.pairwise_iff (fun h => disj_symm h)).1 hdt⟩

theorem partition_flatten_nodup (L : List Nat) (P : List (List Nat))
    (h : partitionCheck L P = true) : P.flatten.Nodup := by
  apply List.nodup_iff_count.2
  intro x
  rw [partition_count L P h]
  split <;> omega

theorem flatten_nodup_parts (P : List (List Nat)) (h : P.flatten.Nodup) :
    (∀ A, A ∈ P → A.Nodup) ∧ P.Pairwise (fun A B => ∀ x, x ∈ A → x ∉ B) := by
  induction P with
  | nil => simp
  | cons A P ih =>
    obtain ⟨hA,hP,hd⟩ := List.nodup_append.1 h
    obtain ⟨hn,hpw⟩ := ih hP
    refine ⟨?_,List.pairwise_cons.2 ⟨?_,hpw⟩⟩
    · intro B hB; rcases List.mem_cons.1 hB with hB | hB
      · subst B; exact hA
      · exact hn B hB
    · intro B hB x hx hxB
      exact hd x hx x (List.mem_flatten.2 ⟨B,hB,hxB⟩) rfl

theorem parent_disjoint (L : List Nat) (P : List (List Nat))
    (hp : partitionCheck L P = true) (A B) (hA : A ∈ P) (hB : B ∈ P) (hne : A ≠ B) :
    ∀ x, x ∈ A → x ∉ B := by
  have hpair := (flatten_nodup_parts P (partition_flatten_nodup L P hp)).2
  exact pairwise_mem (fun A B hd x hxB hxA => hd x hxA hxB) P hpair A B hA hB hne

theorem parent_nodup (L : List Nat) (P : List (List Nat))
    (hp : partitionCheck L P = true) (A) (hA : A ∈ P) : A.Nodup :=
  (flatten_nodup_parts P (partition_flatten_nodup L P hp)).1 A hA

theorem refinement_owner (L : List Nat) (P F : List (List Nat))
    (hp : partitionCheck L P = true) (hf : Refines F P)
    (A C : List Nat) (hA : A ∈ P) (hC : C ∈ F)
    (x : Nat) (hxA : x ∈ A) (hxC : x ∈ C) : Sub C A := by
  obtain ⟨E,hE,hCE⟩ := hf C hC
  by_cases he : A = E
  · subst E; exact hCE
  · exact False.elim (parent_disjoint L P hp A E hA hE he x hxA (hCE x hxC))

theorem filter_blocks_count (F : List (List Nat)) (p : List Nat → Bool) (x : Nat)
    (h : ∀ C, C ∈ F → x ∈ C → p C = true) :
    (F.filter p).flatten.count x = F.flatten.count x := by
  induction F with
  | nil => simp
  | cons C F ih =>
    have iht := ih (by intro E hE; exact h E (by simp [hE]))
    by_cases hx : x ∈ C
    · have hp := h C (by simp) hx
      simp [hp,List.count_append,iht]
    · have hc : C.count x = 0 := List.count_eq_zero.2 hx
      cases hp : p C <;> simp [hp,List.count_append,hc,iht]

theorem apart_partition (L : List Nat) (P F : List (List Nat))
    (hp : partitionCheck L P = true) (hF : partitionCheck L F = true)
    (hf : Refines F P) (A) (hA : A ∈ P) : partitionCheck A (aParts A F) = true := by
  obtain ⟨hn,hc,hl⟩ := partition_parts L F hF
  apply partition_intro
  · intro C hC; exact hn C (List.mem_filter.1 hC).1
  · intro x hx
    have he := filter_blocks_count F (inside · A) x (by
      intro C hC hxC
      exact (inside_iff C A).2 (refinement_owner L P F hp hf A C hA hC x hx hxC))
    change (F.filter (inside · A)).flatten.count x = 1
    rw [he]
    exact hc x (partition_sub L P hp A hA x hx)
  · intro x hx
    obtain ⟨C,hC,hxC⟩ := List.mem_flatten.1 hx
    exact ((inside_iff C A).1 (List.mem_filter.1 hC).2) x hxC

theorem bparts_sub (A B : List Nat) (F : List (List Nat)) :
    ∀ C, C ∈ bParts A B F → Sub C B := by
  intro C hC; exact (inside_iff C B).1 (List.mem_filter.1 hC).2

theorem outside_original (A B : List Nat) (F : List (List Nat)) :
    ∀ C, C ∈ outside A B F → C ∈ F ∧ inside C A = false ∧ inside C B = false := by
  intro C hC
  obtain ⟨hres,hB⟩ := List.mem_filter.1 hC
  obtain ⟨hF,hA⟩ := List.mem_filter.1 hres
  exact ⟨hF,by simpa using hA,by simpa using hB⟩

theorem outside_parent (L : List Nat) (P F : List (List Nat))
    (hf : Refines F P) (A B : List Nat) (C) (hC : C ∈ outside A B F) :
    ∃ E, E ∈ P ∧ E ≠ A ∧ E ≠ B ∧ Sub C E := by
  obtain ⟨hCF,hCA,hCB⟩ := outside_original A B F C hC
  obtain ⟨E,hE,hCE⟩ := hf C hCF
  refine ⟨E,hE,?_,?_,hCE⟩
  · intro he; subst E; have hh := (inside_iff C A).2 hCE; simp [hCA] at hh
  · intro he; subst E; have hh := (inside_iff C B).2 hCE; simp [hCB] at hh
end BinaryExchange
