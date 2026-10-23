import Bridge
namespace VertexGeometry

/-- Partition refinement in original labels. A core child Q must COARSEN the
surviving final partition F. The reverse direction is insufficient for budget
preservation and is never used. -/
def Refines (F Q : List (List Nat)) : Prop :=
  ∀ P, P ∈ F → ∃ R, R ∈ Q ∧ ∀ x, x ∈ P → x ∈ R

theorem refines_trans (F Q R : List (List Nat))
    (hFQ : Refines F Q) (hQR : Refines Q R) : Refines F R := by
  intro P hP
  obtain ⟨Q',hQ,hPQ⟩ := hFQ P hP
  obtain ⟨R',hR,hQR'⟩ := hQR Q' hQ
  exact ⟨R',hR,fun x hx => hQR' x (hPQ x hx)⟩

def Clears (t : RMAF.Tree) (F : List (List Nat)) (v : Vertex) : Prop :=
  ∀ P, P ∈ F → v ∉ RMAF.minimalVertices P t

theorem executable_span_monotone (t : RMAF.Tree) (P Q : List Nat)
    (hsub : ∀ x, x ∈ P → x ∈ Q) :
    ∀ v, v ∈ RMAF.minimalVertices P t → v ∈ RMAF.minimalVertices Q t := by
  intro v hv
  rw [minimalVertices_correct] at hv ⊢
  rcases hv with ⟨a,b,ha,hb,hp⟩
  exact ⟨a,b,selected_leaves_mono P Q t hsub a ha,
    selected_leaves_mono P Q t hsub b hb,hp⟩

theorem refinement_preserves_avoidance (t : RMAF.Tree) (F Q : List (List Nat)) (v : Vertex)
    (hFQ : Refines F Q) (hQ : Clears t Q v) : Clears t F v := by
  intro P hP hv
  obtain ⟨R,hR,hPR⟩ := hFQ P hP
  exact hQ R hR (executable_span_monotone t P R hPR v hv)

/-- This is the CONDITIONAL source-core interface at its first graph consumer.
It is a hypothesis, not a claimed construction or coverage proof. Emitted child
partitions must keep F as a refinement, not merely produce a refinement of F. -/
theorem conditional_core_child_preserves_target (t : RMAF.Tree)
    (F : List (List Nat)) (v : Vertex) (children : List (List (List Nat)))
    (hcore : Clears t F v → ∃ Q, Q ∈ children ∧ Refines F Q ∧ Clears t Q v)
    (hclear : Clears t F v) :
    ∃ Q, Q ∈ children ∧ Refines F Q ∧ Clears t Q v :=
  hcore hclear

/-- A source edge is identified in its ORIGINAL source component and by its
original child address. Tagging is essential: suppression changes no cut cost. -/
abbrev SourceEdge := Nat × Vertex

def InSourceParent (i : Nat) (C : List SourceEdge) : Prop :=
  ∀ e, e ∈ C → e.1 = i

theorem distinct_parent_cut_separation (i j : Nat) (C D : List SourceEdge)
    (hij : i ≠ j) (hC : InSourceParent i C) (hD : InSourceParent j D) :
    ∀ e, e ∈ C → ∀ f, f ∈ D → e ≠ f := by
  intro e he f hf hEq
  have hi := hC e he
  have hj := hD f hf
  have heq := congrArg Prod.fst hEq
  exact hij (hi.symm.trans (heq.trans hj))

/-- Actual nonredundant source cut lists on distinct components compose with
EXACT additive cardinality. There is no same-parent cut-union theorem here. -/
theorem distinct_parent_cut_cost (i j : Nat) (C D : List SourceEdge)
    (hij : i ≠ j) (hC : InSourceParent i C) (hD : InSourceParent j D)
    (hnC : C.Nodup) (hnD : D.Nodup) :
    (C ++ D).Nodup ∧ (C ++ D).length = C.length + D.length := by
  exact ⟨List.nodup_append.2 ⟨hnC,hnD,distinct_parent_cut_separation i j C D hij hC hD⟩,
    List.length_append⟩

/-- Two live parents need exactly the two possible owners at their overlap. -/
theorem two_parent_ownership_cover (F : Nat → List (Vertex → Prop))
    (hd : DisjointParents F) (i j : Nat) (hij : i ≠ j) (v : Vertex) :
    Clear F i v ∨ Clear F j v := by
  classical
  by_cases hi : Occupies F i v
  · exact Or.inr (fun hj => distinct_parents_no_joint_owner F hd i j hij v ⟨hi,hj⟩)
  · exact Or.inl hi

/-- Converts actual original-label block groups to the ownership predicates. -/
def PieceHulls (t : RMAF.Tree) (groups : Nat → List (List Nat)) : Nat → List (Vertex → Prop) :=
  fun i => (groups i).map (selectedLeaves · t)

theorem pieceHulls_occupies (t : RMAF.Tree) (groups : Nat → List (List Nat)) (i : Nat) (v : Vertex) :
    Occupies (PieceHulls t groups) i v ↔
    ∃ P, P ∈ groups i ∧ v ∈ RMAF.minimalVertices P t := by
  simp only [Occupies,PieceHulls,List.mem_map,minimalVertices_correct]
  constructor
  · rintro ⟨P,⟨Q,hQ,rfl⟩,hP⟩; exact ⟨Q,hQ,hP⟩
  · rintro ⟨Q,hQ,hQv⟩; exact ⟨selectedLeaves Q t,⟨Q,hQ,rfl⟩,hQv⟩

theorem pieceHulls_clear (t : RMAF.Tree) (groups : Nat → List (List Nat)) (i : Nat) (v : Vertex) :
    Clear (PieceHulls t groups) i v ↔ Clears t (groups i) v := by
  rw [Clear,pieceHulls_occupies]
  constructor
  · intro h P hP hv; exact h ⟨P,hP,hv⟩
  · intro h ⟨P,hP,hv⟩; exact h P hP hv


theorem pairwise_rel_of_distinct_mem {α : Type} (R : α → α → Prop)
    (hsym : ∀ a b, R a b → R b a) (L : List α) (hp : L.Pairwise R)
    (a b : α) (ha : a ∈ L) (hb : b ∈ L) (hne : a ≠ b) : R a b := by
  induction L with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := List.pairwise_cons.1 hp
    simp only [List.mem_cons] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact False.elim (hne (ha.trans hb.symm))
    · subst a; exact hx b hb
    · subst b; exact hsym x a (hx a ha)
    · exact ih hxs ha hb

theorem agreement_graph_factors (t u : RMAF.Tree) (F : List (List Nat))
    (h : RMAF.agreement t u F = true) :
    RMAF.pairwiseEmbeddings t F = true ∧ RMAF.pairwiseEmbeddings u F = true ∧
      ∀ P, P ∈ F → P ≠ [] := by
  have ht : RMAF.pairwiseEmbeddings t F = true := by
    simp only [RMAF.agreement,Bool.and_eq_true] at h
    simp_all
  have hu : RMAF.pairwiseEmbeddings u F = true := by
    simp only [RMAF.agreement,Bool.and_eq_true] at h
    simp_all
  have hn : F.all (fun P => !P.isEmpty) = true := by
    simp only [RMAF.agreement,RMAF.partitionCheck,Bool.and_eq_true] at h
    simp_all
  refine ⟨ht,hu,?_⟩
  intro P hP he
  have hh := (List.all_eq_true.1 hn) P hP
  simp [he] at hh

/-- Full ownership interface from the original no-rho executable agreement
checker. Groups contain original final blocks, and distinct source parents
have disjoint original labels. No graph-disjointness conclusion is assumed. -/
theorem ownership_from_original_agreement (t u : RMAF.Tree)
    (F : List (List Nat)) (groups : Nat → List (List Nat))
    (hagree : RMAF.agreement t u F = true)
    (hbelongs : ∀ i P, P ∈ groups i → P ∈ F)
    (hlabels : ∀ i j, i ≠ j → ∀ P, P ∈ groups i → ∀ Q, Q ∈ groups j →
      ∀ x, x ∈ P → x ∈ Q → False) : DisjointParents (PieceHulls t groups) := by
  obtain ⟨ht,hu,hn⟩ := agreement_graph_factors t u F hagree
  have hp := (executable_pairwiseEmbeddings t F).1 ht
  intro i j hij P hP Q hQ v hover
  obtain ⟨D,hD,rfl⟩ := List.mem_map.1 hP
  obtain ⟨E,hE,rfl⟩ := List.mem_map.1 hQ
  have hDE : D ≠ E := by
    intro heq
    have hdne := hn D (hbelongs i D hD)
    cases D with
    | nil => exact hdne rfl
    | cons x xs =>
      exact hlabels i j hij _ hD E hE x (by simp) (by rw [←heq]; simp)
  have hd := pairwise_rel_of_distinct_mem
    (fun D E => ∀ v, ¬(Hull (selectedLeaves D t) v ∧ Hull (selectedLeaves E t) v))
    (fun D E h v he => h v ⟨he.2,he.1⟩) F hp D E
    (hbelongs i D hD) (hbelongs j E hE) hDE
  exact hd v hover

theorem executable_clique_survivor_cover (t u : RMAF.Tree)
    (F : List (List Nat)) (groups : Nat → List (List Nat)) (v : Vertex)
    (hagree : RMAF.agreement t u F = true)
    (hbelongs : ∀ i P, P ∈ groups i → P ∈ F)
    (hlabels : ∀ i j, i ≠ j → ∀ P, P ∈ groups i → ∀ Q, Q ∈ groups j →
      ∀ x, x ∈ P → x ∈ Q → False) :
    (Clears t (groups 1) v ∧ Clears t (groups 2) v) ∨
    (Clears t (groups 0) v ∧ Clears t (groups 2) v) ∨
    (Clears t (groups 0) v ∧ Clears t (groups 1) v) := by
  simpa only [pieceHulls_clear] using clique_three_survivor_cover (PieceHulls t groups)
    (ownership_from_original_agreement t u F groups hagree hbelongs hlabels) v

theorem executable_chain_four_cover (t u : RMAF.Tree)
    (F : List (List Nat)) (groups : Nat → List (List Nat)) (v w : Vertex)
    (hagree : RMAF.agreement t u F = true)
    (hbelongs : ∀ i P, P ∈ groups i → P ∈ F)
    (hlabels : ∀ i j, i ≠ j → ∀ P, P ∈ groups i → ∀ Q, Q ∈ groups j →
      ∀ x, x ∈ P → x ∈ Q → False) :
    (Clears t (groups 1) v ∧ Clears t (groups 2) w) ∨
    (Clears t (groups 1) v ∧ Clears t (groups 1) w) ∨
    (Clears t (groups 0) v ∧ Clears t (groups 2) w) ∨
    (Clears t (groups 0) v ∧ Clears t (groups 1) w) := by
  simpa only [pieceHulls_clear] using chain_four_ownership_cover (PieceHulls t groups)
    (ownership_from_original_agreement t u F groups hagree hbelongs hlabels) v w

/-- Original-checker consuming rule for the r=2 chain. Two targets are paid
with ONE B core or with distinct-parent A,C cores. -/
theorem executable_chain_paid_cover (t u : RMAF.Tree)
    (F : List (List Nat)) (groups : Nat → List (List Nat)) (D : List Nat) (v w : Vertex)
    (hagree : RMAF.agreement t u F = true)
    (hbelongs : ∀ i P, P ∈ groups i → P ∈ F)
    (hlabels : ∀ i j, i ≠ j → ∀ P, P ∈ groups i → ∀ Q, Q ∈ groups j →
      ∀ x, x ∈ P → x ∈ Q → False)
    (hB : ∀ P, P ∈ groups 1 → ∀ x, x ∈ P → x ∈ D)
    (hnv : ¬selectedLeaves D t v) (hnw : ¬selectedLeaves D t w)
    (hv : v ∈ RMAF.minimalVertices D t) (hw : w ∈ RMAF.minimalVertices D t)
    (hc : (jointColors D t v w).length = 2) :
    (Clears t (groups 1) v ∧ Clears t (groups 1) w) ∨
      (Clears t (groups 0) v ∧ Clears t (groups 2) w) := by
  have hr := twoJointRegions_of_count_two D t v w hnv hnw hv hw hc
  have hcoinc : Occupies (PieceHulls t groups) 1 v ↔ Occupies (PieceHulls t groups) 1 w := by
    simp only [pieceHulls_occupies]
    constructor
    · rintro ⟨P,hP,hPv⟩
      exact ⟨P,hP,(executable_two_region_coincidence t D P v w hnv hnw hv hw hr (hB P hP)).1 hPv⟩
    · rintro ⟨P,hP,hPw⟩
      exact ⟨P,hP,(executable_two_region_coincidence t D P v w hnv hnw hv hw hr (hB P hP)).2 hPw⟩
  simpa only [pieceHulls_clear] using chain_two_paid_cover (PieceHulls t groups)
    (ownership_from_original_agreement t u F groups hagree hbelongs hlabels) v w hcoinc
end VertexGeometry
