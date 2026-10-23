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
  apply (disjointVertices_iff _ _).mpr
  intro v hvb hva
  exact (disjointVertices_iff _ _).mp h v hva hvb

theorem disjointVertices_mono_left {a a' b : List Vertex}
    (hsub : ∀ v, v ∈ a' → v ∈ a) (h : disjointVertices a b = true) :
    disjointVertices a' b = true := by
  apply (disjointVertices_iff _ _).mpr
  intro v hv
  exact (disjointVertices_iff _ _).mp h v (hsub v hv)

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
  simp only [partitionCheck, Bool.and_eq_true, and_assoc]
  constructor
  · rintro ⟨hn,hc,hl⟩
    refine ⟨by simpa using hn, by simpa using hc, ?_⟩
    intro x hx
    simpa using List.all_eq_true.mp hl x hx
  · rintro ⟨hn,hc,hl⟩
    refine ⟨by simpa using hn, by simpa using hc, ?_⟩
    apply List.all_eq_true.mpr
    intro x hx
    simpa using hl x hx

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

/-- A mark belongs to its own input tree's coordinates. -/
def AvoidsBlock (t : Tree) (b : List Nat) (marks : Vertex → Prop) : Prop :=
  ∀ v, marks v → v ∉ minimalVertices b t

def AvoidsPartition (t : Tree) (bs : List (List Nat)) (marks : Vertex → Prop) : Prop :=
  ∀ b, b ∈ bs → AvoidsBlock t b marks

def Occupied (t : Tree) (bs : List (List Nat)) (v : Vertex) : Prop :=
  ∃ b, b ∈ bs ∧ v ∈ minimalVertices b t

theorem avoidsBlock_mono (t : Tree) (b a : List Nat) (marks : Vertex → Prop)
    (hsub : EmbSub t a b) (h : AvoidsBlock t b marks) : AvoidsBlock t a marks := by
  intro v hv hmem
  exact h v hv (hsub v hmem)

theorem avoidsPartition_replace (t : Tree) (before after : List (List Nat))
    (b b0 b1 : List Nat) (marks : Vertex → Prop)
    (h : AvoidsPartition t (before ++ b :: after) marks)
    (h0 : EmbSub t b0 b) (h1 : EmbSub t b1 b) :
    AvoidsPartition t (before ++ b0 :: b1 :: after) marks := by
  intro c hc
  have hb : AvoidsBlock t b marks := h b (by simp)
  rcases List.mem_append.mp hc with hc | hc
  · exact h c (List.mem_append_left _ hc)
  · rcases List.mem_cons.mp hc with he | hc
    · subst c; exact avoidsBlock_mono t b b0 marks h0 hb
    · rcases List.mem_cons.mp hc with he | hc
      · subst c; exact avoidsBlock_mono t b b1 marks h1 hb
      · exact h c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))

/-- Actual pairwise embedding disjointness ensures every other list occurrence
avoids a vertex used by the displayed block. No index uniqueness is assumed. -/
theorem pairwise_other_avoids (t : Tree) (before after : List (List Nat))
    (b : List Nat) (v : Vertex)
    (h : pairwiseEmbeddings t (before ++ b :: after) = true)
    (hv : v ∈ minimalVertices b t) :
    ∀ c, c ∈ before ++ after → v ∉ minimalVertices c t := by
  induction before with
  | nil =>
    obtain ⟨hall,_⟩ := (pairwiseEmbeddings_cons_iff t b after).mp h
    intro c hc
    exact (disjointVertices_iff _ _).mp (hall c hc) v hv
  | cons a before ih =>
    obtain ⟨hall,htail⟩ := (pairwiseEmbeddings_cons_iff t a (before ++ b :: after)).mp h
    intro c hc
    rcases List.mem_cons.mp hc with he | hc
    · subst c
      intro hvc
      exact (disjointVertices_iff _ _).mp (hall b (by simp)) v hvc hv
    · exact ih htail c hc

theorem replacement_clears_vertex (t : Tree) (before after : List (List Nat))
    (b b0 b1 : List Nat) (v : Vertex)
    (h : pairwiseEmbeddings t (before ++ b :: after) = true)
    (hv : v ∈ minimalVertices b t)
    (h0 : v ∉ minimalVertices b0 t) (h1 : v ∉ minimalVertices b1 t) :
    ¬ Occupied t (before ++ b0 :: b1 :: after) v := by
  rintro ⟨c,hc,hvc⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact pairwise_other_avoids t before after b v h hv c (List.mem_append_left _ hc) hvc
  · rcases List.mem_cons.mp hc with he | hc
    · subst c; exact h0 hvc
    · rcases List.mem_cons.mp hc with he | hc
      · subst c; exact h1 hvc
      · exact pairwise_other_avoids t before after b v h hv c
          (List.mem_append_right _ hc) hvc

theorem replacement_cut_cost (before after : List (List Nat)) (b b0 b1 : List Nat) :
    (before ++ b0 :: b1 :: after).length - 1 =
      ((before ++ b :: after).length - 1) + 1 := by
  simp only [List.length_append, List.length_cons]
  omega

theorem replacement_forest_cost_bound (before after : List (List Nat))
    (b b0 b1 : List Nat) (components : Nat) :
    (before ++ b0 :: b1 :: after).length - components ≤
      (before ++ b :: after).length - components + 1 := by
  have h := replacement_component_count before after b b0 b1
  omega

/-- The global partition and mark-preserving consumer, with every still-needed
local transport and geometry hypothesis exposed in the argument list. -/
theorem agreement_replace_and_clear (t u : Tree) (before after : List (List Nat))
    (b b0 b1 : List Nat) (v : Vertex) (mt mu : Vertex → Prop)
    (h : agreement t u (before ++ b :: after) = true)
    (hmt : AvoidsPartition t (before ++ b :: after) mt)
    (hmu : AvoidsPartition u (before ++ b :: after) mu)
    (h0 : b0 ≠ []) (h1 : b1 ≠ []) (hp : (b0 ++ b1).Perm b)
    (ha0 : restrictionAgrees t u b0 = true) (ha1 : restrictionAgrees t u b1 = true)
    (ht0 : EmbSub t b0 b) (ht1 : EmbSub t b1 b)
    (hu0 : EmbSub u b0 b) (hu1 : EmbSub u b1 b)
    (hdt : disjointVertices (minimalVertices b0 t) (minimalVertices b1 t) = true)
    (hdu : disjointVertices (minimalVertices b0 u) (minimalVertices b1 u) = true)
    (hv : v ∈ minimalVertices b t)
    (hv0 : v ∉ minimalVertices b0 t) (hv1 : v ∉ minimalVertices b1 t) :
    agreement t u (before ++ b0 :: b1 :: after) = true ∧
    ¬ Occupied t (before ++ b0 :: b1 :: after) v ∧
    AvoidsPartition t (before ++ b0 :: b1 :: after) mt ∧
    AvoidsPartition u (before ++ b0 :: b1 :: after) mu ∧
    (before ++ b0 :: b1 :: after).length = (before ++ b :: after).length + 1 := by
  have hag := agreement_replace t u before after b b0 b1 h h0 h1 hp
    ha0 ha1 ht0 ht1 hu0 hu1 hdt hdu
  have ht : pairwiseEmbeddings t (before ++ b :: after) = true := by
    simp only [agreement, Bool.and_eq_true] at h
    exact h.1.2
  exact ⟨hag, replacement_clears_vertex t before after b b0 b1 v ht hv hv0 hv1,
    avoidsPartition_replace t before after b b0 b1 mt hmt ht0 ht1,
    avoidsPartition_replace u before after b b0 b1 mu hmu hu0 hu1,
    replacement_component_count before after b b0 b1⟩

end DegreeTwo
