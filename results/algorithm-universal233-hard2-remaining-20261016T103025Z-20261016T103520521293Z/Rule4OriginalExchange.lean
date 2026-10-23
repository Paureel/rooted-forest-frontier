import Safety
import Forest

/-! Uniform original-graph lemmas for the Rule4 exchange. These lemmas do not
assume the exchange or the desired branch cover. Every hull is the actual
unsuppressed ordinary RMAF embedding via the completed bridge. -/
namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

theorem sibling_regions (p v : RMAF.Vertex)
    (hp : v ≠ p) (hl : v ≠ p ++ [false]) (hr : v ≠ p ++ [true]) :
    region v (p ++ [false]) = region v (p ++ [true]) := by
  induction p generalizing v with
  | nil =>
    cases v with
    | nil => exact False.elim (hp rfl)
    | cons s v =>
      cases v with
      | nil => cases s <;> simp_all
      | cons t v => cases s <;> simp [region]
  | cons s p ih =>
    cases v with
    | nil => cases s <;> rfl
    | cons t v =>
      by_cases he : t = s
      · subst t
        have hp' : v ≠ p := fun h => hp (congrArg (s :: ·) h)
        have hl' : v ≠ p ++ [false] := fun h => hl (congrArg (s :: ·) h)
        have hr' : v ≠ p ++ [true] := fun h => hr (congrArg (s :: ·) h)
        simpa [region] using ih v hp' hl' hr'
      · simp [region,he]

theorem sibling_path_cases {p v : RMAF.Vertex}
    (h : PathAt v (p ++ [false]) (p ++ [true])) :
    v = p ++ [false] ∨ v = p ∨ v = p ++ [true] := by
  by_cases hl : v = p ++ [false]
  · exact Or.inl hl
  by_cases hp : v = p
  · exact Or.inr (Or.inl hp)
  by_cases hr : v = p ++ [true]
  · exact Or.inr (Or.inr hr)
  exact False.elim ((path_region_ne _ _ _ h (Ne.symm hl) (Ne.symm hr))
    (sibling_regions p v hp hl hr))

/-- Adjoining one terminal can add only the path to an old terminal.
This is proved in the original address tree before any suppression. -/
theorem hull_adjoin_subset (P Q : RMAF.Vertex → Prop) (u z : RMAF.Vertex)
    (hu : P u) (hq : ∀ v, Q v → P v ∨ v = z) :
    ∀ v, Hull Q v → Hull P v ∨ PathAt v u z := by
  intro v hv
  by_cases hp : Hull P v
  · exact Or.inl hp
  right
  apply Classical.byContradiction
  intro hn
  have hPv : ¬P v := fun hh => hp ⟨v,v,hh,hh,.endpointL v v⟩
  have mono := (avoids_iff_monochromatic P v hPv).1 hp
  have huz : region v u = region v z := by
    apply Classical.byContradiction
    intro he
    exact hn (region_ne_path v u z he)
  have hQv : ¬Q v := by
    intro hh
    rcases hq v hh with hh | hh
    · exact hPv hh
    · subst v
      exact hn (.endpointR u z)
  have hmono : ∀ x y, Q x → Q y → SameRegion v x y := by
    intro x y hx hy
    have one : ∀ x, Q x → region v x = region v u := by
      intro x hx
      rcases hq x hx with hh | rfl
      · exact mono x u hh hu
      · exact huz.symm
    exact (one x hx).trans (one y hy).symm
  exact ((avoids_iff_monochromatic Q v hQv).2 hmono) hv

/-- A nontrivial selected component at a cherry leaf contains the actual
original parent, by a one-edge walk from that leaf. -/
theorem nonsingleton_hull_parent {T : Tree} {p : RMAF.Vertex} {a b : Nat}
    (hc : CherryAt T p a b) (B : List Nat) (ha : a ∈ B)
    (hd : ∃ d, d ∈ B ∧ d ∈ leaves T ∧ d ≠ a) :
    p ∈ minimalVertices B T := by
  obtain ⟨d,hd,hdl,hda⟩ := hd
  obtain ⟨v,hv⟩ := leaf_exists hdl
  have hua := (minimalVertices_terminal B T _ a (cherry_left hc)).2 ha
  have hvd := (minimalVertices_terminal B T v d hv).2 hd
  have hvne : v ≠ p ++ [false] := by
    intro he
    subst v
    have hh := (cherry_left hc).symm.trans hv
    exact hda (Tree.leaf.inj (Option.some.inj hh)).symm
  exact walk_from_leaf_visits_parent (cherry_left hc)
    (minimalVertices_connected B T _ v hua hvd) hvne

/-- Literal target extension: the new E embedding is contained in the old B
embedding plus the removed singleton b leaf. No outside-clearance premise. -/
theorem target_extension_subset {T : Tree} (hn : (leaves T).Nodup)
    {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b)
    (B E : List Nat) (ha : a ∈ B)
    (hd : ∃ d, d ∈ B ∧ d ∈ leaves T ∧ d ≠ a)
    (hE : ∀ x, x ∈ E → x ∈ B ∨ x = b) :
    ∀ v, v ∈ minimalVertices E T →
      v ∈ minimalVertices B T ∨ v = p ++ [true] := by
  have hparent := nonsingleton_hull_parent hc B ha hd
  have hanchor : selectedLeaves B T (p ++ [false]) :=
    (selected_at_leaf B T _ a (cherry_left hc)).2 ha
  have hsub : ∀ v, selectedLeaves E T v → selectedLeaves B T v ∨ v = p ++ [true] := by
    intro v hv
    obtain ⟨x,hx,hvx⟩ := (selected_decompose_label E T v).1 hv
    have hl : LeafAt T v x := (leafAt_selected T v x).2 hvx
    rcases hE x hx with hx | rfl
    · exact Or.inl ((selected_at_leaf B T v x hl).2 hx)
    · exact Or.inr (leaf_unique hn hl (cherry_right hc))
  intro v hv
  rcases hull_adjoin_subset (selectedLeaves B T) (selectedLeaves E T)
      (p ++ [false]) (p ++ [true]) hanchor hsub v
      ((minimalVertices_correct E T v).1 hv) with hh | hh
  · exact Or.inl ((minimalVertices_correct B T v).2 hh)
  · rcases sibling_path_cases hh with rfl | rfl | hh
    · exact Or.inl ((minimalVertices_terminal B T _ a (cherry_left hc)).2 ha)
    · exact Or.inl hparent
    · exact Or.inr hh

/-- Uniform target clearance from every untouched ORIGINAL agreement block.
The caller supplies just the old agreement and literal block membership. -/
theorem target_extension_clear {T S : Tree} {F : List (List Nat)}
    (hn : (leaves T).Nodup) (hF : agreement T S F = true)
    {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b)
    {B H E : List Nat} (hB : B ∈ F) (hH : H ∈ F) (hne : H ≠ B)
    (hb : b ∉ H) (ha : a ∈ B)
    (hd : ∃ d, d ∈ B ∧ d ∈ leaves T ∧ d ≠ a)
    (hE : ∀ x, x ∈ E → x ∈ B ∨ x = b) :
    disjointVertices (minimalVertices E T) (minimalVertices H T) = true := by
  have hp := (agreement_graph_factors T S F hF).1
  have hold : ∀ v, v ∈ minimalVertices B T → v ∈ minimalVertices H T → False := by
    intro v hv hw
    have he := checked_support_unique T F hp B H hB hH v hv hw
    exact hne he.symm
  apply (VertexGeometry.executable_disjointVertices T E H).2
  intro v hv
  have hvE := (minimalVertices_correct E T v).2 hv.1
  have hvH := (minimalVertices_correct H T v).2 hv.2
  rcases target_extension_subset hn hc B E ha hd hE v hvE with hh | he
  · exact hold v hh hvH
  · subst v
    exact hb ((minimalVertices_terminal H T _ b (cherry_right hc)).1 hvH)

theorem subtreeLabels_at_leaf {T : Tree} {u : RMAF.Vertex} {x : Nat}
    (h : LeafAt T u x) : subtreeLabels T u = [x] := by
  induction u generalizing T with
  | nil =>
    have ht : T = .leaf x := Option.some.inj h
    subst T
    rfl
  | cons s u ih =>
    cases T with
    | leaf y => simp [LeafAt,subtree] at h
    | node l r => cases s <;> exact ih h

/-- Every selected leaf outside an actual original cherry is in its parent
region, so its original hull cannot use that cherry parent. -/
theorem cherry_parent_clear {T : Tree} {p : RMAF.Vertex} {a b : Nat}
    (hc : CherryAt T p a b) (D : List Nat) (ha : a ∉ D) (hb : b ∉ D) :
    p ∉ minimalVertices D T := by
  have one : ∀ v, selectedLeaves D T v → region p v = 2 := by
    intro v hv
    obtain ⟨x,hx,hvx⟩ := (selected_decompose_label D T v).1 hv
    have hl : LeafAt T v x := (leafAt_selected T v x).2 hvx
    have hzero : region p v ≠ 0 := by
      intro hz
      have hpre : p ++ [false] <+: v :=
        (child_region_prefix p false v).1 (by simpa using hz)
      have hxs : x ∈ subtreeLabels T (p ++ [false]) :=
        (subtreeLabels_prefix T _ x).2 ⟨v,hl,hpre⟩
      have he : subtreeLabels T (p ++ [false]) = [a] :=
        subtreeLabels_at_leaf (cherry_left hc)
      have hxa : x = a := by simpa [he] using hxs
      exact ha (hxa ▸ hx)
    have hone : region p v ≠ 1 := by
      intro hz
      have hpre : p ++ [true] <+: v :=
        (child_region_prefix p true v).1 (by simpa using hz)
      have hxs : x ∈ subtreeLabels T (p ++ [true]) :=
        (subtreeLabels_prefix T _ x).2 ⟨v,hl,hpre⟩
      have he : subtreeLabels T (p ++ [true]) = [b] :=
        subtreeLabels_at_leaf (cherry_right hc)
      have hxb : x = b := by simpa [he] using hxs
      exact hb (hxb ▸ hx)
    have hthree : region p v ≠ 3 := by
      intro hz
      have he := (region_eq_three_iff p v).1 hz
      exact cherry_parent_not_terminal hc hl he
    have hle := region_le_three p v
    omega
  intro hm
  obtain ⟨u,v,hu,hv,hp⟩ := (minimalVertices_correct D T p).1 hm
  have hun : u ≠ p := fun he => by subst u; have hh := one p hu; simp [region_self] at hh
  have hvn : v ≠ p := fun he => by subst v; have hh := one p hv; simp [region_self] at hh
  exact (path_region_ne p u v hp hun hvn) ((one u hu).trans (one v hv).symm)

/-- The two new target components remain mutually disjoint after b is added.
The only split premise is the literal D/K embedding separation supplied by the
proved final-block cluster transfer; no exchange/cover premise is present. -/
theorem target_mutual_clear {T : Tree} (hn : (leaves T).Nodup)
    {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b)
    (D K E : List Nat) (ha : a ∈ K) (hna : a ∉ D) (hnb : b ∉ D)
    (hDK : disjointVertices (minimalVertices D T) (minimalVertices K T) = true)
    (hE : ∀ x, x ∈ E → x ∈ K ∨ x = b) :
    disjointVertices (minimalVertices D T) (minimalVertices E T) = true := by
  have hold := (executable_disjointVertices T D K).1 hDK
  have hparent := cherry_parent_clear hc D hna hnb
  have hanchor : selectedLeaves K T (p ++ [false]) :=
    (selected_at_leaf K T _ a (cherry_left hc)).2 ha
  have hsub : ∀ v, selectedLeaves E T v → selectedLeaves K T v ∨ v = p ++ [true] := by
    intro v hv
    obtain ⟨x,hx,hvx⟩ := (selected_decompose_label E T v).1 hv
    have hl : LeafAt T v x := (leafAt_selected T v x).2 hvx
    rcases hE x hx with hx | rfl
    · exact Or.inl ((selected_at_leaf K T v x hl).2 hx)
    · exact Or.inr (leaf_unique hn hl (cherry_right hc))
  apply (executable_disjointVertices T D E).2
  intro v hv
  rcases hull_adjoin_subset (selectedLeaves K T) (selectedLeaves E T)
    (p ++ [false]) (p ++ [true]) hanchor hsub v hv.2 with hh | hh
  · exact hold v ⟨hv.1,hh⟩
  · have hdv := (minimalVertices_correct D T v).2 hv.1
    rcases sibling_path_cases hh with rfl | rfl | rfl
    · exact hna ((minimalVertices_terminal D T _ a (cherry_left hc)).1 hdv)
    · exact hparent hdv
    · exact hnb ((minimalVertices_terminal D T _ b (cherry_right hc)).1 hdv)

/-- Original source subtree -> transferred final-block split -> mutual target
clearance after reattaching b. All disjointness conclusions are derived. -/
theorem original_split_target_clear {T S U : Tree}
    (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
    {p q : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b)
    (hq : treeAt S q = some U) (B : List Nat)
    (hagree : restrictionAgrees T S B = true)
    (ha : a ∈ B) (hau : a ∉ leaves U) (hbu : b ∉ leaves U) :
    disjointVertices
      (minimalVertices (yes B ((leaves U).contains ·)) T)
      (minimalVertices (b :: no B ((leaves U).contains ·)) T) = true := by
  have split := (descendant_agreed_split T S U q B hnS hq hagree).2.1
  apply target_mutual_clear hnT hc
    (yes B ((leaves U).contains ·)) (no B ((leaves U).contains ·))
    (b :: no B ((leaves U).contains ·))
  · simp [no,ha,hau]
  · simp [yes,hau]
  · simp [yes,hbu]
  · exact split
  · intro x hx
    simpa [List.mem_cons,or_comm] using hx

theorem leaf_parent_hull {T : Tree} {p : RMAF.Vertex} {side : Bool} {a : Nat}
    (hc : LeafAt T (p ++ [side]) a) (B : List Nat) (ha : a ∈ B)
    (hd : ∃ d, d ∈ B ∧ d ∈ leaves T ∧ d ≠ a) :
    p ∈ minimalVertices B T := by
  obtain ⟨d,hd,hdl,hda⟩ := hd
  obtain ⟨v,hv⟩ := leaf_exists hdl
  have hua := (minimalVertices_terminal B T _ a hc).2 ha
  have hvd := (minimalVertices_terminal B T v d hv).2 hd
  have hvne : v ≠ p ++ [side] := by
    intro he
    subst v
    have hh := hc.symm.trans hv
    exact hda (Tree.leaf.inj (Option.some.inj hh)).symm
  exact walk_from_leaf_visits_parent hc
    (minimalVertices_connected B T _ v hua hvd) hvne

/-- In the source's disputed case, c is an actual singleton original block.
This is a global F consequence of the original source checker. -/
theorem source_c_singleton {T S : Tree} {F : List (List Nat)}
    (hF : agreement T S F = true) {p : RMAF.Vertex} {a c : Nat}
    (hc : CherryAt S p a c) {B : List Nat} (hB : B ∈ F)
    (ha : a ∈ B) (hcB : c ∉ B)
    (hd : ∃ d, d ∈ B ∧ d ∈ leaves S ∧ d ≠ a) : [c] ∈ F := by
  have checks := source_agreement_checks hF
  have hparent := nonsingleton_hull_parent hc B ha hd
  obtain ⟨C,hC,hcC⟩ := partitionCheck_covers _ F checks.1 c
    (leafAt_label S _ c (cherry_right hc))
  have only : ∀ x, x ∈ C → x = c := by
    intro x hx
    by_cases he : x = c
    · exact he
    have hpc := leaf_parent_hull (cherry_right hc) C hcC
      ⟨x,hx,block_labels checks.1 hC hx,he⟩
    have hCB := checked_support_unique S F checks.2 C B hC hB p hpc hparent
    exact False.elim (hcB (hCB ▸ hcC))
  have he := block_singleton_of_only checks.1 hC hcC only
  simpa [he] using hC

/-- If the old B occupies an original boundary's parent, no untouched block
may cross it. This derives source clearance from actual original embeddings. -/
theorem source_boundary_mono {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (hF : agreement T S F = true)
    {B H : List Nat} (hB : B ∈ F) (hH : H ∈ F) (hne : H ≠ B)
    {q : RMAF.Vertex} (hq : q ≠ []) (hp : q.dropLast ∈ minimalVertices B S) :
    ∀ x y, x ∈ H → y ∈ H →
      (x ∈ subtreeLabels S q ↔ y ∈ subtreeLabels S q) := by
  have checks := source_agreement_checks hF
  have one : ∀ x y, x ∈ H → y ∈ H →
      x ∈ subtreeLabels S q → y ∈ subtreeLabels S q := by
    intro x y hx hy hxq
    apply Classical.byContradiction
    intro hyq
    obtain ⟨u,hu,hup⟩ := (subtreeLabels_prefix S q x).1 hxq
    obtain ⟨v,hv⟩ := leaf_exists (block_labels checks.1 hH hy)
    have hvp : ¬q <+: v := fun hh => hyq ((subtreeLabels_prefix S q y).2 ⟨v,hv,hh⟩)
    have hpc : q.dropLast ∈ minimalVertices H S := by
      apply (minimalVertices_correct H S _).2
      exact ⟨u,v,(selected_at_leaf H S u x hu).2 hx,
        (selected_at_leaf H S v y hv).2 hy,cut_crossing_path hq hup hvp⟩
    have he := checked_support_unique S F checks.2 H B hH hB _ hpc hp
    exact hne he
  intro x y hx hy
  exact ⟨one x y hx hy,one y x hy hx⟩

/-- The disputed B actually occupies the original X2 boundary parent. -/
theorem crossing_boundary_parent {S : Tree} {q : RMAF.Vertex} (hq : q ≠ [])
    (B : List Nat) {a d : Nat} (ha : a ∈ B) (hd : d ∈ B)
    (hal : a ∈ leaves S) (hdo : d ∈ subtreeLabels S q)
    (hao : a ∉ subtreeLabels S q) : q.dropLast ∈ minimalVertices B S := by
  obtain ⟨u,hu,hup⟩ := (subtreeLabels_prefix S q d).1 hdo
  obtain ⟨v,hv⟩ := leaf_exists hal
  have hvp : ¬q <+: v := fun hh => hao ((subtreeLabels_prefix S q a).2 ⟨v,hv,hh⟩)
  apply (minimalVertices_correct B S _).2
  exact ⟨u,v,(selected_at_leaf B S u d hu).2 hd,
    (selected_at_leaf B S v a hv).2 ha,cut_crossing_path hq hup hvp⟩


theorem two_cut_mem_left {S : Tree} {a b : Nat} {q r : RMAF.Vertex}
    (h : (pendantOriginal S a b).Perm [q,r]) : q ∈ pendantOriginal S a b :=
  h.mem_iff.2 (by simp)
theorem two_cut_mem_right {S : Tree} {a b : Nat} {q r : RMAF.Vertex}
    (h : (pendantOriginal S a b).Perm [q,r]) : r ∈ pendantOriginal S a b :=
  h.mem_iff.2 (by simp)
theorem two_cut_cases {S : Tree} {a b : Nat} {q r v : RMAF.Vertex}
    (h : (pendantOriginal S a b).Perm [q,r]) (hv : v ∈ pendantOriginal S a b) : v = q ∨ v = r := by
  simpa using h.mem_iff.1 hv
theorem two_cut_length {S : Tree} {a b : Nat} {q r : RMAF.Vertex}
    (h : (pendantOriginal S a b).Perm [q,r]) : (pendantOriginal S a b).length = 2 := by
  simpa using h.length_eq

theorem two_perm_cases {u v q r : RMAF.Vertex} (h : [u,v].Perm [q,r]) :
    (u = q ∧ v = r) ∨ (u = r ∧ v = q) := by
  have hu : u = q ∨ u = r := by simpa using h.mem_iff.1 (by simp : u ∈ [u,v])
  rcases hu with he | he
  · subst u
    have hv : v = r := by simpa using h.cons_inv
    exact Or.inl ⟨rfl,hv⟩
  · subst u
    have hs : [r,v].Perm [r,q] := h.trans (List.Perm.swap r q [])
    have hv : v = q := by simpa using hs.cons_inv
    exact Or.inr ⟨rfl,hv⟩

theorem literalThree_swap_perm (S : Tree) (q r : RMAF.Vertex) :
    (literalThree S q r).Perm (literalThree S r q) := by
  have he : (leaves S).filter (fun x => !(subtreeLabels S q).contains x && !(subtreeLabels S r).contains x) =
      (leaves S).filter (fun x => !(subtreeLabels S r).contains x && !(subtreeLabels S q).contains x) := by
    congr 1
    funext x
    exact Bool.and_comm _ _
  dsimp only [literalThree]
  rw [he]
  exact List.Perm.swap _ _ _

theorem refines_two_cut_order {S : Tree} {a b : Nat} {q r u v : RMAF.Vertex}
    (h : (pendantOriginal S a b).Perm [q,r]) (he : pendantOriginal S a b = [u,v])
    {F : List (List Nat)} (hf : VertexGeometry.Refines F (literalThree S u v)) :
    VertexGeometry.Refines F (literalThree S q r) := by
  have hp : [u,v].Perm [q,r] := by rw [←he]; exact h
  rcases two_perm_cases hp with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · subst u; subst v; exact hf
  · subst u; subst v
    intro C hC
    obtain ⟨D,hD,hsub⟩ := hf C hC
    exact ⟨D,(literalThree_swap_perm S r q).mem_iff.1 hD,hsub⟩

end Universal233.Rule4
