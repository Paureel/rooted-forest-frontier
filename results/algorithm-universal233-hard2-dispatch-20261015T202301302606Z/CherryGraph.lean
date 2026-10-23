import CherryReverse

namespace ForestState
open RMAF RestrictionBridge

inductive CherryAt (a b : Nat) : Tree → Vertex → Prop where
  | straight : CherryAt a b (.node (.leaf a) (.leaf b)) []
  | swapped : CherryAt a b (.node (.leaf b) (.leaf a)) []
  | left {l r : Tree} {w : Vertex} : CherryAt a b l w → CherryAt a b (.node l r) (false :: w)
  | right {l r : Tree} {w : Vertex} : CherryAt a b r w → CherryAt a b (.node l r) (true :: w)

theorem cherry_at_exists (t : Tree) (a b : Nat) (h : cherry a b t = true) :
    ∃ w, CherryAt a b t w := by
  induction t with
  | leaf x => simp [cherry] at h
  | node l r hl hr =>
    simp only [cherry,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h
    rcases h with ((⟨e1,e2⟩ | ⟨e1,e2⟩) | h1) | h2
    · subst l; subst r; exact ⟨[],CherryAt.straight⟩
    · subst l; subst r; exact ⟨[],CherryAt.swapped⟩
    · obtain ⟨w,hw⟩ := hl h1; exact ⟨false :: w,CherryAt.left hw⟩
    · obtain ⟨w,hw⟩ := hr h2; exact ⟨true :: w,CherryAt.right hw⟩

theorem CherryAt.labels {t : Tree} {a b : Nat} {w : Vertex} (h : CherryAt a b t w) :
    a ∈ leaves t ∧ b ∈ leaves t := by
  induction h with
  | straight => simp [leaves]
  | swapped => simp [leaves]
  | left h ih => simp [leaves,ih]
  | right h ih => simp [leaves,ih]

theorem CherryAt.symm {t : Tree} {a b : Nat} {w : Vertex} (h : CherryAt a b t w) :
    CherryAt b a t w := by
  induction h with
  | straight => exact CherryAt.swapped
  | swapped => exact CherryAt.straight
  | left h ih => exact CherryAt.left ih
  | right h ih => exact CherryAt.right ih

theorem span_nonempty_of_selected (t : Tree) (B : List Nat) (x : Nat)
    (hx : x ∈ leaves t) (hB : x ∈ B) : (rootedSpan B t).isEmpty = false := by
  obtain ⟨u,hu⟩ := restriction_exists t B ⟨x,hx,hB⟩
  rw [span_empty,hu]
  rfl

theorem CherryAt.parent_in_span {t : Tree} {a b : Nat} {w : Vertex}
    (h : CherryAt a b t w) (B : List Nat) (ha : a ∈ B) : w ∈ rootedSpan B t := by
  induction h with
  | straight => simp [rootedSpan,ha]
  | swapped => simp [rootedSpan,ha]
  | @left l r w h ih =>
    have ne := span_nonempty_of_selected l B a h.labels.1 ha
    simp [rootedSpan,ne,prependSide,ih]
  | @right l r w h ih =>
    have ne := span_nonempty_of_selected r B a h.labels.1 ha
    simp [rootedSpan,ne,prependSide,ih]

theorem CherryAt.parent_in_minimal {t : Tree} {a b : Nat} {w : Vertex}
    (h : CherryAt a b t w) (B : List Nat) (ha : a ∈ B) (hb : b ∉ B)
    (extra : ∃ x, x ∈ leaves t ∧ x ∈ B ∧ x ≠ a) : w ∈ minimalVertices B t := by
  induction h with
  | straight =>
    obtain ⟨x,hx,hxB,hxa⟩ := extra
    simp only [leaves,List.mem_append,List.mem_singleton] at hx
    rcases hx with he | he
    · exact False.elim (hxa he)
    · subst x; exact False.elim (hb hxB)
  | swapped =>
    obtain ⟨x,hx,hxB,hxa⟩ := extra
    simp only [leaves,List.mem_append,List.mem_singleton] at hx
    rcases hx with he | he
    · subst x; exact False.elim (hb hxB)
    · exact False.elim (hxa he)
  | @left l r w h ih =>
    have ne := span_nonempty_of_selected l B a h.labels.1 ha
    cases er : (rootedSpan B r).isEmpty with
    | false =>
      have hw := h.parent_in_span B ha
      simp [minimalVertices,ne,er,prependSide,hw]
    | true =>
      have exl : ∃ x, x ∈ leaves l ∧ x ∈ B ∧ x ≠ a := by
        obtain ⟨x,hx,hxB,hxa⟩ := extra
        rcases List.mem_append.1 hx with hxl | hxr
        · exact ⟨x,hxl,hxB,hxa⟩
        · have hf := span_nonempty_of_selected r B x hxr hxB
          simp [er] at hf
      have hw := ih exl
      simp [minimalVertices,ne,er,prependSide,hw]
  | @right l r w h ih =>
    have ne := span_nonempty_of_selected r B a h.labels.1 ha
    cases el : (rootedSpan B l).isEmpty with
    | false =>
      have hw := h.parent_in_span B ha
      simp [minimalVertices,ne,el,prependSide,hw]
    | true =>
      have exr : ∃ x, x ∈ leaves r ∧ x ∈ B ∧ x ≠ a := by
        obtain ⟨x,hx,hxB,hxa⟩ := extra
        rcases List.mem_append.1 hx with hxl | hxr
        · have hf := span_nonempty_of_selected l B x hxl hxB
          simp [el] at hf
        · exact ⟨x,hxr,hxB,hxa⟩
      have hw := ih exr
      simp [minimalVertices,ne,el,prependSide,hw]

theorem non_singleton_extra (L B : List Nat) (a : Nat) (ha : a ∈ B)
    (sub : B ⊆ L) (nd : B.Nodup) (hne : B ≠ [a]) :
    ∃ x, x ∈ L ∧ x ∈ B ∧ x ≠ a := by
  by_cases ex : ∃ x, x ∈ B ∧ x ≠ a
  · obtain ⟨x,hx,hxa⟩ := ex
    exact ⟨x,sub hx,hx,hxa⟩
  · have hs : B ⊆ [a] := by
      intro x hx
      have he : x = a := by
        by_cases he : x = a
        · exact he
        · exact False.elim (ex ⟨x,hx,he⟩)
      simpa [he]
    exact False.elim (hne (subset_singleton_eq B a (List.ne_nil_of_mem ha) hs nd))

theorem separated_cherry_forces_singleton (t : Tree) (F : List (List Nat))
    (a b : Nat) (ht : cherry a b t = true) (hp : partitionCheck (leaves t) F = true)
    (A B : List Nat) (hA : A ∈ F) (hB : B ∈ F) (ha : a ∈ A) (hb : b ∈ B)
    (hab : b ∉ A) (hba : a ∉ B)
    (clear : disjointVertices (minimalVertices A t) (minimalVertices B t) = true) :
    A = [a] ∨ B = [b] := by
  by_cases hsa : A = [a]
  · exact Or.inl hsa
  · by_cases hsb : B = [b]
    · exact Or.inr hsb
    · obtain ⟨w,hw⟩ := cherry_at_exists t a b ht
      have subA : A ⊆ leaves t := by
        intro x hx; exact checked_label (leaves t) F hp hA hx
      have subB : B ⊆ leaves t := by
        intro x hx; exact checked_label (leaves t) F hp hB hx
      have exA := non_singleton_extra (leaves t) A a ha subA
        (checked_block_nodup (leaves t) F hp A hA) hsa
      have exB := non_singleton_extra (leaves t) B b hb subB
        (checked_block_nodup (leaves t) F hp B hB) hsb
      have wa := hw.parent_in_minimal A ha hab exA
      have wb := hw.symm.parent_in_minimal B hb hba exB
      exact False.elim ((clear_iff _ _).1 clear w wa wb)

end ForestState

namespace ForestState
open RMAF RestrictionBridge

theorem disjoint_symmetry (A B : List Vertex) :
    disjointVertices A B = true ↔ disjointVertices B A = true := by
  rw [clear_iff,clear_iff,clear_symm]

theorem pairwise_distinct_members (t : Tree) (F : List (List Nat))
    (hp : pairwiseEmbeddings t F = true) (A B : List Nat)
    (ha : A ∈ F) (hb : B ∈ F) (hne : A ≠ B) :
    disjointVertices (minimalVertices A t) (minimalVertices B t) = true := by
  induction F with
  | nil => simp at ha
  | cons C F ih =>
    have hh : (∀ D ∈ F, disjointVertices (minimalVertices C t) (minimalVertices D t) = true) ∧
        pairwiseEmbeddings t F = true := by simpa [pairwiseEmbeddings,List.all_eq_true] using hp
    rcases List.mem_cons.1 ha with heA | hA
    · subst A
      have hB : B ∈ F := (List.mem_cons.1 hb).resolve_left (Ne.symm hne)
      exact hh.1 B hB
    · rcases List.mem_cons.1 hb with heB | hB
      · subst B
        exact (disjoint_symmetry _ _).2 (hh.1 A hA)
      · exact ih hh.2 hA hB

theorem actual_separated_cherry_singleton (t : Tree) (ss : List Tree) (F : List (List Nat))
    (a b : Nat) (h : agrees (some t) ss F = true) (ht : cherry a b t = true)
    (A B : List Nat) (hA : A ∈ F) (hB : B ∈ F) (ha : a ∈ A) (hb : b ∈ B)
    (hab : b ∉ A) (hba : a ∉ B) : A = [a] ∨ B = [b] := by
  have hp := agrees_parts (some t) ss F h
  have hne : A ≠ B := by intro he; subst B; exact hba ha
  exact separated_cherry_forces_singleton t F a b ht hp.2.1 A B hA hB ha hb hab hba
    (pairwise_distinct_members t F hp.2.2.2.1 A B hA hB hne)

end ForestState
