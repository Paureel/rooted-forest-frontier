import Rule4Exchange

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

theorem lca_prefix_left (u v : RMAF.Vertex) : lca u v <+: u := by
  induction u generalizing v with
  | nil => simp [lca]
  | cons s u ih =>
    cases v with
    | nil => simp [lca]
    | cons t v =>
      by_cases he : s = t
      · subst t
        obtain ⟨tail,ht⟩ := ih v
        exact ⟨tail,by simpa [lca] using congrArg (s :: ·) ht⟩
      · simp [lca,he]

theorem lca_prefix_right (u v : RMAF.Vertex) : lca u v <+: v := by
  induction u generalizing v with
  | nil => simp [lca]
  | cons s u ih =>
    cases v with
    | nil => simp [lca]
    | cons t v =>
      by_cases he : s = t
      · subst t
        obtain ⟨tail,ht⟩ := ih v
        exact ⟨tail,by simpa [lca] using congrArg (s :: ·) ht⟩
      · simp [lca,he]

theorem path_prefix_closed (w : RMAF.Vertex) {u v z : RMAF.Vertex}
    (hu : w <+: u) (hv : w <+: v) (hp : PathAt z u v) : w <+: z := by
  induction w generalizing u v z with
  | nil => simp
  | cons s w ih =>
    obtain ⟨ut,rfl⟩ := hu
    obtain ⟨vt,rfl⟩ := hv
    cases z with
    | nil => exact False.elim (path_root_same_impossible s (w ++ ut) (w ++ vt) hp)
    | cons t z =>
      by_cases he : t = s
      · subst t
        obtain ⟨tail,ht⟩ := ih (List.prefix_append _ _) (List.prefix_append _ _)
          ((path_same_side s z (w ++ ut) (w ++ vt)).1 hp)
        exact ⟨tail,congrArg (s :: ·) ht⟩
      · have hst : s = !t := by cases s <;> cases t <;> simp_all
        subst s
        exact False.elim (path_other_same_impossible t z (w ++ ut) (w ++ vt) hp)

/-- Follow an original root-to-leaf address until the first edge leaving P.
This is finite list recursion; no geometric exit assertion is assumed. -/
theorem first_prefix_exit (P : RMAF.Vertex → Prop) (w tail : RMAF.Vertex)
    (hw : P w) (hx : ¬P (w ++ tail)) :
    ∃ q, q ≠ [] ∧ q <+: w ++ tail ∧ P q.dropLast ∧ ¬P q := by
  induction tail generalizing w with
  | nil => exact False.elim (hx (by simpa using hw))
  | cons s tail ih =>
    by_cases hs : P (w ++ [s])
    · have hn : ¬P ((w ++ [s]) ++ tail) := by simpa [List.append_assoc] using hx
      obtain ⟨q,hne,hpre,hparent,hout⟩ := ih (w ++ [s]) hs hn
      exact ⟨q,hne,by simpa [List.append_assoc] using hpre,hparent,hout⟩
    · exact ⟨w ++ [s],by simp,⟨tail,by simp [List.append_assoc]⟩,by simpa using hw,hs⟩

/-- All leaves under the pair's ORIGINAL LCA are endpoints or lie below an
actual outgoing original pendant head. This controls arbitrary outside taxa. -/
theorem pair_lca_label_cover {S : Tree} (hn : (leaves S).Nodup)
    {a b : Nat} {u v : RMAF.Vertex} (hu : LeafAt S u a) (hv : LeafAt S v b) :
    ∀ x, x ∈ subtreeLabels S (lca u v) →
      x = a ∨ x = b ∨ ∃ q, q ∈ pendantOriginal S a b ∧ x ∈ subtreeLabels S q := by
  intro x hx
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxb : x = b
  · exact Or.inr (Or.inl hxb)
  right;right
  obtain ⟨z,hz,hwz⟩ := (subtreeLabels_prefix S (lca u v) x).1 hx
  have hw : lca u v ∈ minimalVertices [a,b] S :=
    (pair_minimal_path hn hu hv _).2 (lca_on_path u v)
  have hzout : z ∉ minimalVertices [a,b] S := by
    intro hh
    have hm := (minimalVertices_terminal [a,b] S z x hz).1 hh
    simp [hxa,hxb] at hm
  obtain ⟨tail,htail⟩ := hwz
  have hout : ¬(fun z => z ∈ minimalVertices [a,b] S) (lca u v ++ tail) := by simpa [←htail] using hzout
  obtain ⟨q,hq,hqz,hparent,hnot⟩ := first_prefix_exit
    (fun z => z ∈ minimalVertices [a,b] S) (lca u v) tail hw hout
  have hqz' : q <+: z := by simpa [←htail] using hqz
  have hvalid : Valid S q := valid_ancestor hz.valid hqz'
  exact ⟨q,(pendantOriginal_spec S a b q).2 ⟨hvalid,hq,hparent,hnot⟩,
    (subtreeLabels_prefix S q x).2 ⟨z,hz,hqz'⟩⟩

theorem pendant_under_pair_lca {S : Tree} (hn : (leaves S).Nodup)
    {a b : Nat} {u v : RMAF.Vertex} (hu : LeafAt S u a) (hv : LeafAt S v b)
    {q : RMAF.Vertex} (hq : q ∈ pendantOriginal S a b) : lca u v <+: q := by
  have hp := (pendantOriginal_spec S a b q).1 hq
  have hpath := (pair_minimal_path hn hu hv _).1 hp.2.2.1
  exact (path_prefix_closed (lca u v) (lca_prefix_left u v) (lca_prefix_right u v) hpath).trans
    (List.dropLast_prefix q)

/-- The no-X2 subcase already respects the literal source partition. Its
outside labels are handled at the original pair LCA, including a root LCA. -/
theorem retained_a_block_refines {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (hF : agreement T S F = true)
    {a b c : Nat} (hab : a ≠ b) (hcS : HasCherry a c S)
    {q r : RMAF.Vertex} (hcuts : (pendantOriginal S a b).Perm [q,r])
    (hql : subtreeLabels S q = [c]) {B : List Nat} (hB : B ∈ F)
    (ha : a ∈ B) (hcB : c ∉ B) (hb : [b] ∈ F)
    (hno : ∀ x, x ∈ B → x ∉ subtreeLabels S r)
    (hd : ∃ d, d ∈ B ∧ d ∈ leaves S ∧ d ≠ a) :
    VertexGeometry.Refines F (literalThree S q r) := by
  have checks := source_agreement_checks hF
  have hal : a ∈ leaves S := block_labels checks.1 hB ha
  have hbl : b ∈ leaves S := block_labels checks.1 hb (by simp)
  obtain ⟨u,hu⟩ := leaf_exists hal
  obtain ⟨v,hv⟩ := leaf_exists hbl
  let w := lca u v
  have hwvalid : Valid S w := valid_ancestor hu.valid (lca_prefix_left u v)
  obtain ⟨W,hW⟩ := hwvalid
  have hWtree : treeAt S w = some W := by rw [treeAt_eq_subtree]; exact hW
  have hWlabels := subtreeLabels_eq_leaves hW
  have haW : a ∈ leaves W := by
    rw [←hWlabels]
    exact (subtreeLabels_prefix S w a).2 ⟨u,hu,lca_prefix_left u v⟩
  have cover : ∀ x, x ∈ leaves W → x = a ∨ x = b ∨ x = c ∨ x ∈ subtreeLabels S r := by
    intro x hx
    rcases pair_lca_label_cover hn hu hv x (by change x ∈ subtreeLabels S w; rw [hWlabels]; exact hx) with hh | hh | ⟨p,hp,hxp⟩
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · have he : p = q ∨ p = r := two_cut_cases hcuts hp
      rcases he with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (by simpa [hql] using hxp)))
      · exact Or.inr (Or.inr (Or.inr hxp))
  have hbB : b ∉ B := by
    intro hh
    have eq := shared_label_block_equal checks.1 checks.2 hB hb hh (by simp)
    exact hab (by simpa [eq] using ha)
  have hc := source_sibling_singleton hF hcS hB ha hcB hd
  obtain ⟨d,hdB,hdl,hda⟩ := hd
  have hdW : d ∉ leaves W := by
    intro hh
    rcases cover d hh with he | he | he | he
    · exact hda he
    · exact hbB (he ▸ hdB)
    · exact hcB (he ▸ hdB)
    · exact hno d hdB he
  have hBparent : w ∈ minimalVertices B S := crossing_occupies S W w B hn hWtree
    (by intro x hx; exact block_labels checks.1 hB hx) ⟨⟨a,ha,haW⟩,⟨d,hdB,hdW⟩⟩
  have hr : r ∈ pendantOriginal S a b := two_cut_mem_right hcuts
  have hrw := pendant_under_pair_lca hn hu hv hr
  have Xinside : ∀ x, x ∈ subtreeLabels S r → x ∈ leaves W := by
    intro x hx
    obtain ⟨z,hz,hrz⟩ := (subtreeLabels_prefix S r x).1 hx
    rw [←hWlabels]
    exact (subtreeLabels_prefix S w x).2 ⟨z,hz,hrw.trans hrz⟩
  have mono : ∀ H, H ∈ F → ∀ x y, x ∈ H → y ∈ H →
      (x ∈ subtreeLabels S r ↔ y ∈ subtreeLabels S r) := by
    have one : ∀ H, H ∈ F → ∀ x y, x ∈ H → y ∈ H →
        x ∈ subtreeLabels S r → y ∈ subtreeLabels S r := by
      intro H hH x y hx hy hxR
      by_cases he : H = B
      · subst H; exact False.elim (hno x hx hxR)
      apply Classical.byContradiction
      intro hyR
      have haH : a ∉ H := fun hh => he (shared_label_block_equal checks.1 checks.2 hH hB hh ha)
      have hbH : b ∉ H := by
        intro hh
        have eq := shared_label_block_equal checks.1 checks.2 hH hb hh (by simp)
        have hxB : x = b := by simpa [eq] using hx
        have out := source_label_outside_pendant hr (Or.inr rfl) hbl
        exact out (hxB ▸ hxR)
      have hcH : c ∉ H := by
        intro hh
        have eq := shared_label_block_equal checks.1 checks.2 hH hc hh (by simp)
        have hxC : x = c := by simpa [eq] using hx
        have hq : q ∈ pendantOriginal S a b := two_cut_mem_left hcuts
        have hqr : q ≠ r := by
          have hn' := pendantOriginal_nodup S a b
          simpa using hcuts.nodup_iff.1 hn'
        have hdis := pendant_labelsets_disjoint hn hq hr hqr
        exact hdis c (by simp [hql]) (hxC ▸ hxR)
      have hyW : y ∉ leaves W := by
        intro hh
        rcases cover y hh with he | he | he | he
        · exact haH (he ▸ hy)
        · exact hbH (he ▸ hy)
        · exact hcH (he ▸ hy)
        · exact hyR he
      have hHp : w ∈ minimalVertices H S := crossing_occupies S W w H hn hWtree
        (by intro z hz; exact block_labels checks.1 hH hz) ⟨⟨x,hx,Xinside x hxR⟩,⟨y,hy,hyW⟩⟩
      exact he (checked_support_unique S F checks.2 H B hH hB w hHp hBparent)
    intro H hH x y hx hy
    exact ⟨one H hH x y hx hy,one H hH y x hy hx⟩
  intro H hH
  have hne := (agreement_graph_factors T S F hF).2.2 H hH
  cases H with
  | nil => contradiction
  | cons x xs =>
    by_cases hxc : x = c
    · have he : (x :: xs) = [c] := shared_label_block_equal checks.1 checks.2 hH hc (x := c) (by simp [hxc]) (by simp)
      exact ⟨subtreeLabels S q,by simp [literalThree],by simpa [he,hql]⟩
    · by_cases hxR : x ∈ subtreeLabels S r
      · exact ⟨subtreeLabels S r,by simp [literalThree],by intro y hy; exact (mono _ hH x y (by simp) hy).1 hxR⟩
      · refine ⟨(leaves S).filter (fun y => !(subtreeLabels S q).contains y && !(subtreeLabels S r).contains y),by simp [literalThree],?_⟩
        intro y hy
        have hyR : y ∉ subtreeLabels S r := fun hh => hxR ((mono _ hH x y (by simp) hy).2 hh)
        have hyc : y ≠ c := by
          intro he
          have eq := shared_label_block_equal checks.1 checks.2 hH hc (he ▸ hy) (by simp)
          have hh : x = c := by simpa [eq] using (show x ∈ x :: xs from by simp)
          exact hxc hh
        simp [hql,block_labels checks.1 hH hy,hyc,hyR]
end Universal233.Rule4
