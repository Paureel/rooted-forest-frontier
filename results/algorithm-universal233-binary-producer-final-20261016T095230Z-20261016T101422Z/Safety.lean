import Components

namespace Universal233.HardParent
open RMAF CoreGraph Integration VertexGeometry CutRealization List

theorem subtreeLabels_sublist (S : Tree) (q : RMAF.Vertex) :
    subtreeLabels S q <+ leaves S := by
  induction q generalizing S with
  | nil => exact List.Sublist.refl _
  | cons s q ih =>
    cases S with
    | leaf x => exact List.nil_sublist _
    | node l r =>
      cases s
      · exact (ih l).trans (List.sublist_append_left _ _)
      · exact (ih r).trans (List.sublist_append_right _ _)

theorem pendant_labelsets_disjoint {S : Tree} {a b : Nat} {q r : RMAF.Vertex}
    (hn : (leaves S).Nodup) (hq : q ∈ pendantOriginal S a b)
    (hr : r ∈ pendantOriginal S a b) (hne : q ≠ r) :
    ∀ x, x ∈ subtreeLabels S q → x ∉ subtreeLabels S r := by
  have hab := pendant_incomparable hq hr hne
  intro x hx hy
  obtain ⟨u,hu,hup⟩ := (subtreeLabels_prefix S q x).1 hx
  obtain ⟨v,hv,hvp⟩ := (subtreeLabels_prefix S r x).1 hy
  have he := leaf_unique hn hu hv
  rw [he] at hup
  rcases List.prefix_or_prefix_of_prefix hup hvp with hh | hh
  · exact hab.1 hh
  · exact hab.2 hh

theorem literalThree_partition {S : Tree} {a b : Nat} {q r : RMAF.Vertex}
    (hn : (leaves S).Nodup) (hq : q ∈ pendantOriginal S a b)
    (hr : r ∈ pendantOriginal S a b) (hne : q ≠ r)
    (hc : LiteralOriginalThree S q r) :
    partitionCheck (leaves S) (literalThree S q r) = true := by
  let A := subtreeLabels S q
  let B := subtreeLabels S r
  let C := (leaves S).filter (fun x => !A.contains x && !B.contains x)
  have hA : A.Nodup := (subtreeLabels_sublist S q).nodup hn
  have hB : B.Nodup := (subtreeLabels_sublist S r).nodup hn
  have hC : C.Nodup := hn.filter _
  have hdis : ∀ x, x ∈ A → x ∉ B := pendant_labelsets_disjoint hn hq hr hne
  have count_one : ∀ x, x ∈ leaves S → (A ++ B ++ C).count x = 1 := by
    intro x hx
    by_cases hxa : x ∈ A
    · have hxb := hdis x hxa
      have hxc : x ∉ C := by simp [C,hxa]
      simp [List.count_append,hA.count,hB.count,hC.count,hxa,hxb,hxc]
    · by_cases hxb : x ∈ B
      · have hxc : x ∉ C := by simp [C,hxb]
        simp [List.count_append,hA.count,hB.count,hC.count,hxa,hxb,hxc]
      · have hxc : x ∈ C := by simp [C,hx,hxa,hxb]
        simp [List.count_append,hA.count,hB.count,hC.count,hxa,hxb,hxc]
  simp only [partitionCheck,Bool.and_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · have ha := hc.nonempty_left
    have hb := hc.nonempty_right
    have hroot := hc.nonempty_root
    have nonempty : ∀ L : List Nat, L ≠ [] → (!L.isEmpty) = true := by
      intro L hL
      cases L with
      | nil => exact False.elim (hL rfl)
      | cons x xs => rfl
    simp only [literalThree,List.all_cons,List.all_nil,Bool.and_eq_true]
    exact ⟨nonempty _ ha,nonempty _ hb,nonempty _ hroot,True.intro⟩
  · apply List.all_eq_true.2
    intro x hx
    apply beq_iff_eq.2
    simpa [literalThree,A,B,C,List.append_assoc] using count_one x hx
  · apply List.all_eq_true.2
    intro x hx
    apply List.contains_iff_mem.2
    have hcases : x ∈ A ∨ x ∈ B ∨ x ∈ C := by simpa [literalThree,A,B,C] using hx
    rcases hcases with hh | hh | hh
    · exact (subtreeLabels_sublist S q).subset hh
    · exact (subtreeLabels_sublist S r).subset hh
    · exact (List.mem_filter.1 hh).1

theorem agreement_cherry_source_labels {T S : Tree} {F : List (List Nat)}
    (ha : agreement T S F = true) {p : RMAF.Vertex} {a b : Nat}
    (hc : CherryAt T p a b) : a ∈ leaves S ∧ b ∈ leaves S := by
  have hpt : partitionCheck (leaves T) F = true := by
    simp only [agreement,Bool.and_eq_true] at ha
    exact ha.1.1.1.1
  have hps := (source_agreement_checks ha).1
  have one : ∀ x, x ∈ leaves T → x ∈ leaves S := by
    intro x hx
    obtain ⟨B,hB,hxB⟩ := partitionCheck_covers _ F hpt x hx
    exact block_labels hps hB hxB
  exact ⟨one a (leafAt_label T _ a (cherry_left hc)),
    one b (leafAt_label T _ b (cherry_right hc))⟩

/-- Consumer with the two actual original child cuts named. Source path, actual
components, nonempty leaf sets and agreement refinement are all constructed. -/
theorem actual_hard2_named_safety {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (ha : agreement T S F = true)
    {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b)
    {q r : RMAF.Vertex} (hcuts : pendantOriginal S a b = [q,r]) :
    LiteralOriginalThree S q r ∧ partitionCheck (leaves S) (literalThree S q r) = true ∧
      ([a] ∈ F ∨ [b] ∈ F ∨ VertexGeometry.Refines F (literalThree S q r)) := by
  have hq : q ∈ pendantOriginal S a b := by simp [hcuts]
  have hr : r ∈ pendantOriginal S a b := by simp [hcuts]
  have hne : q ≠ r := by
    have hh := pendantOriginal_nodup S a b
    simpa [hcuts] using hh
  have hq' := (pendantOriginal_spec S a b q).1 hq
  have hr' := (pendantOriginal_spec S a b r).1 hr
  have hcomp := literalOriginalThree_construct hn (agreement_cherry_source_labels ha hc).1 hq hr hne
  exact ⟨hcomp,literalThree_partition hn hq hr hne hcomp,
    original_hard_parent_refinement hn ha hc hq'.2.1 hq'.2.2.1 hq'.2.2.2 hr'.2.1 hr'.2.2.1 hr'.2.2.2⟩

/-- Figure16 hard-parent safety from exactly TWO actual source pendant edges.
The caller supplies only the original agreement, the actual unsuppressed target
cherry, distinct original source labels, and the exact two-edge count. -/
theorem actual_hard2_source_safety {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (ha : agreement T S F = true)
    {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b)
    (h2 : (pendantOriginal S a b).length = 2) :
    ∃ q r, pendantOriginal S a b = [q,r] ∧ LiteralOriginalThree S q r ∧
      partitionCheck (leaves S) (literalThree S q r) = true ∧
      ([a] ∈ F ∨ [b] ∈ F ∨ VertexGeometry.Refines F (literalThree S q r)) := by
  have he := List.eq_getElem_of_length_eq_two (pendantOriginal S a b) h2
  exact ⟨_,_,he,actual_hard2_named_safety hn ha hc he⟩

def ActualCherry (T : Tree) (a b : Nat) : Prop :=
  ∃ p, CherryAt T p a b ∨ CherryAt T p b a

theorem pendantOriginal_swap (S : Tree) (a b : Nat) :
    pendantOriginal S a b = pendantOriginal S b a := by
  have he := minimalVertices_ext [a,b] [b,a] S
    (by intro x hx; simp [Bool.or_comm])
  simp only [pendantOriginal,he]

/-- Sibling orientation is not part of the consumer's original cherry. -/
theorem actual_hard2_unordered_safety {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (ha : agreement T S F = true)
    {a b : Nat} (hc : ActualCherry T a b)
    (h2 : (pendantOriginal S a b).length = 2) :
    ∃ q r, pendantOriginal S a b = [q,r] ∧ LiteralOriginalThree S q r ∧
      partitionCheck (leaves S) (literalThree S q r) = true ∧
      ([a] ∈ F ∨ [b] ∈ F ∨ VertexGeometry.Refines F (literalThree S q r)) := by
  obtain ⟨p,hc | hc⟩ := hc
  · exact actual_hard2_source_safety hn ha hc h2
  · have h2' : (pendantOriginal S b a).length = 2 := by rw [←pendantOriginal_swap S a b]; exact h2
    obtain ⟨q,r,hcuts,hcomp,hpart,hs⟩ := actual_hard2_source_safety hn ha hc h2'
    refine ⟨q,r,?_,hcomp,hpart,?_⟩
    · rw [pendantOriginal_swap S a b]; exact hcuts
    · rcases hs with hs | hs | hs
      · exact Or.inr (Or.inl hs)
      · exact Or.inl hs
      · exact Or.inr (Or.inr hs)

theorem hard2_endpoints_in_root {S : Tree} {a b : Nat} {q r : RMAF.Vertex}
    (hq : q ∈ pendantOriginal S a b) (hr : r ∈ pendantOriginal S a b)
    (ha : a ∈ leaves S) (hb : b ∈ leaves S) :
    a ∈ (leaves S).filter (fun x => !(subtreeLabels S q).contains x && !(subtreeLabels S r).contains x) ∧
    b ∈ (leaves S).filter (fun x => !(subtreeLabels S q).contains x && !(subtreeLabels S r).contains x) := by
  have haq := source_label_outside_pendant hq (Or.inl rfl) ha
  have har := source_label_outside_pendant hr (Or.inl rfl) ha
  have hbq := source_label_outside_pendant hq (Or.inr rfl) hb
  have hbr := source_label_outside_pendant hr (Or.inr rfl) hb
  simp [ha,hb,haq,har,hbq,hbr]

#print axioms actual_hard2_source_safety
#print axioms actual_hard2_named_safety
#print axioms original_pendant_spec
#print axioms literalOriginalThree_construct
end Universal233.HardParent
