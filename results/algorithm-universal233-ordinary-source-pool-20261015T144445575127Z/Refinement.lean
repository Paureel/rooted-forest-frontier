import PendantExclusion

namespace Universal233.HardParent
open RMAF CoreGraph Integration VertexGeometry

theorem child_region_prefix (p : RMAF.Vertex) (s : Bool) (v : RMAF.Vertex) :
    region p v = (if s then 1 else 0) ↔ p ++ [s] <+: v := by
  induction p generalizing v with
  | nil =>
    cases v with
    | nil => cases s <;> simp [region]
    | cons t v => cases s <;> cases t <;> simp [region]
  | cons t p ih =>
    cases v with
    | nil => cases s <;> simp [region]
    | cons u v =>
      by_cases ht : t = u
      · subst u
        simpa [region] using ih v
      · cases s <;> simp [region,ht]

theorem cut_crossing_path {q u v : RMAF.Vertex} (hq : q ≠ [])
    (hu : q <+: u) (hv : ¬q <+: v) : PathAt q.dropLast u v := by
  rcases List.eq_nil_or_concat q with h | ⟨p,s,h⟩
  · exact False.elim (hq h)
  · have he : q = p ++ [s] := by simpa only [List.concat_eq_append] using h
    rw [he] at hu hv ⊢
    have hru := (child_region_prefix p s u).2 hu
    have hrv : region p v ≠ (if s then 1 else 0) := fun hh => hv ((child_region_prefix p s v).1 hh)
    simpa using region_ne_path p u v (fun hh => hrv (hh ▸ hru))

theorem subtreeLabels_prefix (S : Tree) (p : RMAF.Vertex) (x : Nat) :
    x ∈ subtreeLabels S p ↔ ∃ v, LeafAt S v x ∧ p <+: v := by
  induction p generalizing S with
  | nil =>
    simp only [subtreeLabels]
    constructor
    · intro hx
      obtain ⟨v,hv⟩ := (singleton_selected_exists S x).2 hx
      exact ⟨v,(leafAt_selected S v x).2 hv,List.nil_prefix⟩
    · rintro ⟨v,hv,hp⟩
      exact leafAt_label S v x hv
  | cons s p ih =>
    cases S with
    | leaf y =>
      simp only [subtreeLabels,List.not_mem_nil,false_iff]
      rintro ⟨v,hv,⟨tail,rfl⟩⟩
      simp [LeafAt,subtree] at hv
    | node l r =>
      simp only [subtreeLabels]
      constructor
      · intro hx
        obtain ⟨v,hv,hp⟩ := (ih (if s then r else l)).1 hx
        exact ⟨s :: v,by simpa [LeafAt,subtree] using hv,by simpa using hp⟩
      · rintro ⟨v,hv,⟨tail,rfl⟩⟩
        apply (ih (if s then r else l)).2
        exact ⟨p ++ tail,by simpa [LeafAt,subtree] using hv,⟨tail,rfl⟩⟩

theorem source_agreement_checks {T S : Tree} {F : List (List Nat)}
    (ha : agreement T S F = true) :
    partitionCheck (leaves S) F = true ∧ pairwiseEmbeddings S F = true := by
  simp only [agreement,Bool.and_eq_true] at ha
  exact ⟨ha.1.1.1.2,ha.2⟩

/-- Every block of the ORIGINAL agreement respects every original pendant cut.
The proof uses actual source hull collision at that edge's original parent. -/
theorem agreement_respects_pendant {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (ha : agreement T S F = true) {p : RMAF.Vertex} {a b : Nat}
    (hc : CherryAt T p a b) {B : List Nat} (hB : B ∈ F) (haB : a ∈ B) (hbB : b ∈ B)
    {q : RMAF.Vertex} (hq : q ≠ []) (hp : q.dropLast ∈ minimalVertices [a,b] S)
    (hqo : q ∉ minimalVertices [a,b] S) :
    ∀ C, C ∈ F → ∀ x y, x ∈ C → y ∈ C →
      (x ∈ subtreeLabels S q ↔ y ∈ subtreeLabels S q) := by
  have hchecks := source_agreement_checks ha
  have excluded := original_common_block_excluded hn ha hc hB haB hbB
  have hBparent : q.dropLast ∈ minimalVertices B S :=
    executable_span_monotone S [a,b] B (by intro x hx; simpa using (show x = a ∨ x = b from by simpa using hx).elim (fun e => e ▸ haB) (fun e => e ▸ hbB)) _ hp
  have one : ∀ C, C ∈ F → ∀ x y, x ∈ C → y ∈ C →
      x ∈ subtreeLabels S q → y ∈ subtreeLabels S q := by
    intro C hC x y hx hy hxq
    by_cases he : C = B
    · subst C
      exact False.elim (excluded q hq hp hqo x hxq hx)
    · apply Classical.byContradiction
      intro hyq
      obtain ⟨u,hu,hup⟩ := (subtreeLabels_prefix S q x).1 hxq
      obtain ⟨v,hv⟩ := (singleton_selected_exists S y).2 (block_labels hchecks.1 hC hy)
      have hv' : LeafAt S v y := (leafAt_selected S v y).2 hv
      have hvp : ¬q <+: v := fun hh => hyq ((subtreeLabels_prefix S q y).2 ⟨v,hv',hh⟩)
      have hCparent : q.dropLast ∈ minimalVertices C S := by
        apply (minimalVertices_correct C S _).2
        exact ⟨u,v,(selected_at_leaf C S u x hu).2 hx,
          (selected_at_leaf C S v y hv').2 hy,cut_crossing_path hq hup hvp⟩
      exact he (checked_support_unique S F hchecks.2 C B hC hB _ hCparent hBparent)
  intro C hC x y hx hy
  exact ⟨one C hC x y hx hy,one C hC y x hy hx⟩

/-- Label refinement of the three LITERAL original leaf sets, without asking
that any agreement cut set contain the two source edges. -/
theorem original_hard_parent_refinement {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (ha : agreement T S F = true) {p : RMAF.Vertex} {a b : Nat}
    (hc : CherryAt T p a b) {q r : RMAF.Vertex}
    (hq : q ≠ []) (hqp : q.dropLast ∈ minimalVertices [a,b] S) (hqo : q ∉ minimalVertices [a,b] S)
    (hr : r ≠ []) (hrp : r.dropLast ∈ minimalVertices [a,b] S) (hro : r ∉ minimalVertices [a,b] S) :
    [a] ∈ F ∨ [b] ∈ F ∨ VertexGeometry.Refines F (literalThree S q r) := by
  rcases actual_cherry_endpoint_alternative ha hc with hs | hs | ⟨B,hB,haB,hbB⟩
  · exact Or.inl hs
  · exact Or.inr (Or.inl hs)
  · right; right
    have hchecks := source_agreement_checks ha
    have hqmono := agreement_respects_pendant hn ha hc hB haB hbB hq hqp hqo
    have hrmono := agreement_respects_pendant hn ha hc hB haB hbB hr hrp hro
    intro C hC
    have hnC := (agreement_graph_factors T S F ha).2.2 C hC
    cases C with
    | nil => exact False.elim (hnC rfl)
    | cons x xs =>
      by_cases hxq : x ∈ subtreeLabels S q
      · refine ⟨subtreeLabels S q,by simp [literalThree],?_⟩
        intro y hy
        exact (hqmono _ hC x y (by simp) hy).1 hxq
      · by_cases hxr : x ∈ subtreeLabels S r
        · refine ⟨subtreeLabels S r,by simp [literalThree],?_⟩
          intro y hy
          exact (hrmono _ hC x y (by simp) hy).1 hxr
        · refine ⟨(leaves S).filter (fun y => !(subtreeLabels S q).contains y && !(subtreeLabels S r).contains y),by simp [literalThree],?_⟩
          intro y hy
          have hyq : y ∉ subtreeLabels S q := fun hh => hxq ((hqmono _ hC x y (by simp) hy).2 hh)
          have hyr : y ∉ subtreeLabels S r := fun hh => hxr ((hrmono _ hC x y (by simp) hy).2 hh)
          simp [block_labels hchecks.1 hC hy,hyq,hyr]
end Universal233.HardParent
