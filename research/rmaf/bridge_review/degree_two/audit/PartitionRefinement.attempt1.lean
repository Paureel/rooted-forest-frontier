import RMAF

/-! Conditional consumer of an actual two-block refinement. The original
Boolean agreement predicate remains unchanged. Local geometric/transport
premises are explicit and are not established by this module alone. -/
namespace DegreeTwo
open RMAF

/-- Exact support containment in one actual input tree. -/
def EmbSub (t : Tree) (a b : List Nat) : Prop :=
  ∀ v, v ∈ minimalVertices a t → v ∈ minimalVertices b t

theorem disjointVertices_iff (a b : List Vertex) :
    disjointVertices a b = true ↔ ∀ v, v ∈ a → v ∉ b := by
  simp [disjointVertices]

theorem disjointVertices_symm {a b : List Vertex}
    (h : disjointVertices a b = true) : disjointVertices b a = true := by
  apply disjointVertices_iff.mpr
  intro v hvb hva
  exact disjointVertices_iff.mp h v hva hvb

theorem disjointVertices_mono_left {a a' b : List Vertex}
    (hsub : ∀ v, v ∈ a' → v ∈ a) (h : disjointVertices a b = true) :
    disjointVertices a' b = true := by
  apply disjointVertices_iff.mpr
  intro v hv
  exact disjointVertices_iff.mp h v (hsub v hv)

theorem disjointVertices_mono_right {a b b' : List Vertex}
    (hsub : ∀ v, v ∈ b' → v ∈ b) (h : disjointVertices a b = true) :
    disjointVertices a b' = true :=
  disjointVertices_symm (disjointVertices_mono_left hsub (disjointVertices_symm h))

theorem pairwiseEmbeddings_cons_iff (t : Tree) (b : List Nat) (bs : List (List Nat)) :
    pairwiseEmbeddings t (b :: bs) = true ↔
      (∀ c, c ∈ bs → disjointVertices (minimalVertices b t) (minimalVertices c t) = true) ∧
      pairwiseEmbeddings t bs = true := by
  simp [pairwiseEmbeddings]

/-- The old block may occur anywhere in the partition list. -/
theorem pairwiseEmbeddings_replace (t : Tree) (before after : List (List Nat))
    (b b0 b1 : List Nat)
    (h : pairwiseEmbeddings t (before ++ b :: after) = true)
    (h0 : EmbSub t b0 b) (h1 : EmbSub t b1 b)
    (h01 : disjointVertices (minimalVertices b0 t) (minimalVertices b1 t) = true) :
    pairwiseEmbeddings t (before ++ b0 :: b1 :: after) = true := by
  induction before with
  | nil =>
    obtain ⟨hall, htail⟩ := (pairwiseEmbeddings_cons_iff t b after).mp h
    apply (pairwiseEmbeddings_cons_iff t b0 (b1 :: after)).mpr
    constructor
    · intro c hc
      rcases List.mem_cons.mp hc with he | hc
      · subst c; exact h01
      · exact disjointVertices_mono_left h0 (hall c hc)
    · exact (pairwiseEmbeddings_cons_iff t b1 after).mpr
        ⟨fun c hc => disjointVertices_mono_left h1 (hall c hc), htail⟩
  | cons c before ih =>
    obtain ⟨hall, htail⟩ := (pairwiseEmbeddings_cons_iff t c (before ++ b :: after)).mp h
    apply (pairwiseEmbeddings_cons_iff t c (before ++ b0 :: b1 :: after)).mpr
    constructor
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hall d (List.mem_append_left _ hd)
      · rcases List.mem_cons.mp hd with he | hd
        · subst d
          exact disjointVertices_mono_right h0 (hall b (by simp))
        · rcases List.mem_cons.mp hd with he | hd
          · subst d
            exact disjointVertices_mono_right h1 (hall b (by simp))
          · exact hall d (List.mem_append_right _ (List.mem_cons_of_mem _ hd))
    · exact ih htail

theorem flatten_replace_perm (before after : List (List Nat)) (b b0 b1 : List Nat)
    (hp : (b0 ++ b1).Perm b) :
    (before ++ b0 :: b1 :: after).flatten.Perm (before ++ b :: after).flatten := by
  simpa only [List.flatten_append, List.flatten_cons, List.append_assoc] using
    (hp.append_right after.flatten).append_left before.flatten

theorem partitionCheck_iff (labels : List Nat) (bs : List (List Nat)) :
    partitionCheck labels bs = true ↔
      (∀ b, b ∈ bs → b ≠ []) ∧
      (∀ x, x ∈ labels → bs.flatten.count x = 1) ∧
      (∀ x, x ∈ bs.flatten → x ∈ labels) := by
  simp [partitionCheck, Bool.and_eq_true, and_assoc]

theorem partitionCheck_replace (labels : List Nat) (before after : List (List Nat))
    (b b0 b1 : List Nat) (h : partitionCheck labels (before ++ b :: after) = true)
    (h0 : b0 ≠ []) (h1 : b1 ≠ []) (hp : (b0 ++ b1).Perm b) :
    partitionCheck labels (before ++ b0 :: b1 :: after) = true := by
  obtain ⟨hne,hcount,hlabels⟩ := (partitionCheck_iff labels _).mp h
  have hperm := flatten_replace_perm before after b b0 b1 hp
  apply (partitionCheck_iff labels _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hne c (List.mem_append_left _ hc)
    · rcases List.mem_cons.mp hc with he | hc
      · subst c; exact h0
      · rcases List.mem_cons.mp hc with he | hc
        · subst c; exact h1
        · exact hne c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))
  · intro x hx
    exact (hperm.count_eq x).trans (hcount x hx)
  · intro x hx
    exact hlabels x (hperm.mem_iff.mp hx)

/-- Concrete original-predicate consumer, conditional on the explicit local
geometric/refinement facts. This theorem does not manufacture those facts. -/
theorem agreement_replace (t u : Tree) (before after : List (List Nat))
    (b b0 b1 : List Nat) (h : agreement t u (before ++ b :: after) = true)
    (h0 : b0 ≠ []) (h1 : b1 ≠ []) (hp : (b0 ++ b1).Perm b)
    (ha0 : restrictionAgrees t u b0 = true) (ha1 : restrictionAgrees t u b1 = true)
    (ht0 : EmbSub t b0 b) (ht1 : EmbSub t b1 b)
    (hu0 : EmbSub u b0 b) (hu1 : EmbSub u b1 b)
    (hdt : disjointVertices (minimalVertices b0 t) (minimalVertices b1 t) = true)
    (hdu : disjointVertices (minimalVertices b0 u) (minimalVertices b1 u) = true) :
    agreement t u (before ++ b0 :: b1 :: after) = true := by
  simp only [agreement, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨hpt,hpu⟩,ha⟩,ht⟩,hu⟩ := h
  refine ⟨⟨⟨⟨partitionCheck_replace _ before after b b0 b1 hpt h0 h1 hp,
    partitionCheck_replace _ before after b b0 b1 hpu h0 h1 hp⟩, ?_⟩,
    pairwiseEmbeddings_replace t before after b b0 b1 ht ht0 ht1 hdt⟩,
    pairwiseEmbeddings_replace u before after b b0 b1 hu hu0 hu1 hdu⟩
  apply List.all_eq_true.mpr
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact List.all_eq_true.mp ha c (List.mem_append_left _ hc)
  · rcases List.mem_cons.mp hc with he | hc
    · subst c; exact ha0
    · rcases List.mem_cons.mp hc with he | hc
      · subst c; exact ha1
      · exact List.all_eq_true.mp ha c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))

theorem replacement_component_count (before after : List (List Nat)) (b b0 b1 : List Nat) :
    (before ++ b0 :: b1 :: after).length = (before ++ b :: after).length + 1 := by
  simp
  omega

end DegreeTwo
