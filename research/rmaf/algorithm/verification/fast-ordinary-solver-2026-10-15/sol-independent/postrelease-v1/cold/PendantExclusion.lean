import Restriction

namespace Universal233.HardParent
open RMAF CoreGraph Integration VertexGeometry

/-- The original source has a fork yielding the selected cherry, possibly
below a chain of original ancestors. Siblings ABOVE that fork are unrestricted. -/
inductive PrunedCherry (D : List Nat) (a b : Nat) : Tree → Prop
  | fork {l r} : restrict D l = some (.leaf a) → restrict D r = some (.leaf b) →
      PrunedCherry D a b (.node l r)
  | forkSwap {l r} : restrict D l = some (.leaf b) → restrict D r = some (.leaf a) →
      PrunedCherry D a b (.node l r)
  | left {l r} : PrunedCherry D a b l → a ∉ leaves r → b ∉ leaves r →
      PrunedCherry D a b (.node l r)
  | right {l r} : PrunedCherry D a b r → a ∉ leaves l → b ∉ leaves l →
      PrunedCherry D a b (.node l r)

theorem prunedCherry_labels {D a b T} (h : PrunedCherry D a b T) :
    a ∈ leaves T ∧ b ∈ leaves T := by
  induction h with
  | fork hl hr =>
    exact ⟨List.mem_append_left _ ((restrict_mem hl a).1 (by simp [leaves])).1,
      List.mem_append_right _ ((restrict_mem hr b).1 (by simp [leaves])).1⟩
  | @forkSwap l r hl hr =>
    exact ⟨List.mem_append_right _ ((restrict_mem hr a).1 (by simp [leaves])).1,
      List.mem_append_left _ ((restrict_mem hl b).1 (by simp [leaves])).1⟩
  | left h ha hb ih => exact ⟨by simp [leaves,ih.1],by simp [leaves,ih.2]⟩
  | right h ha hb ih => exact ⟨by simp [leaves,ih.1],by simp [leaves,ih.2]⟩

theorem prunedCherry_of_restrict {D : List Nat} {T U : Tree} {a b : Nat}
    (hn : (leaves T).Nodup) (hr : restrict D T = some U)
    (hc : HasCherry a b U) : PrunedCherry D a b T := by
  induction T generalizing U with
  | leaf x =>
    simp only [restrict] at hr
    split at hr
    · cases Option.some.inj hr; cases hc
    · contradiction
  | node l r ihl ihr =>
    obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.1 hn
    have labs {V : Tree} (hV : restrict D l = some V) (hch : HasCherry a b V) :
        a ∉ leaves r ∧ b ∉ leaves r := by
      have h := hasCherry_labels hch
      exact ⟨fun ha => hdis a ((restrict_mem hV a).1 h.1).1 a ha rfl,
        fun hb => hdis b ((restrict_mem hV b).1 h.2).1 b hb rfl⟩
    have rabs {V : Tree} (hV : restrict D r = some V) (hch : HasCherry a b V) :
        a ∉ leaves l ∧ b ∉ leaves l := by
      have h := hasCherry_labels hch
      exact ⟨fun ha => hdis a ha a ((restrict_mem hV a).1 h.1).1 rfl,
        fun hb => hdis b hb b ((restrict_mem hV b).1 h.2).1 rfl⟩
    cases hl : restrict D l with
    | none =>
      cases hv : restrict D r with
      | none => simp [restrict,hl,hv] at hr
      | some V =>
        have he : V = U := Option.some.inj (by simpa [restrict,hl,hv] using hr)
        subst U
        exact .right (ihr hnr hv hc) (rabs hv hc).1 (rabs hv hc).2
    | some V =>
      cases hv : restrict D r with
      | none =>
        have he : V = U := Option.some.inj (by simpa [restrict,hl,hv] using hr)
        subst U
        exact .left (ihl hnl hl hc) (labs hl hc).1 (labs hl hc).2
      | some W =>
        have he : Tree.node V W = U := Option.some.inj (by simpa [restrict,hl,hv] using hr)
        subst U
        cases hc with
        | here => exact .fork hl hv
        | swap => exact .forkSwap hl hv
        | left h => exact .left (ihl hnl hl h) (labs hl h).1 (labs hl h).2
        | right h => exact .right (ihr hnr hv h) (rabs hv h).1 (rabs hv h).2

theorem rootedSpan_child (D : List Nat) (l r : Tree) (s : Bool) (v : RMAF.Vertex) :
    s :: v ∈ rootedSpan D (.node l r) ↔ v ∈ rootedSpan D (if s then r else l) := by
  cases s
  · simp only [rootedSpan_correct,selectedLeaves,reach_join_side,Bool.false_eq_true,↓reduceIte]
  · simp only [rootedSpan_correct,selectedLeaves,reach_join_right,↓reduceIte]

theorem rootspan_nonempty {D : List Nat} {T : Tree} {x : Nat}
    (hx : x ∈ leaves T) (hD : x ∈ D) : (rootedSpan D T).isEmpty = false := by
  obtain ⟨v,hv⟩ := (singleton_selected_exists T x).2 hx
  have hs := (selected_at_leaf D T v x ((leafAt_selected T v x).2 hv)).2 hD
  have hr : [] ∈ rootedSpan D T := (rootedSpan_correct D T []).2
    ((reach_root _).2 ⟨v,hs⟩)
  cases hh : rootedSpan D T with
  | nil => simp [hh] at hr
  | cons v vs => rfl

theorem rootspan_empty {D : List Nat} {T : Tree}
    (h : ∀ x, x ∈ leaves T → x ∉ D) : rootedSpan D T = [] := by
  apply (rootspan_empty_from_correct D T (rootedSpan_correct D T [])).2
  rintro ⟨v,hv⟩
  obtain ⟨x,hx,hs⟩ := (selected_decompose_label D T v).1 hv
  exact h x ((singleton_selected_exists T x).1 ⟨v,hs⟩) hx

theorem rootedSpan_ext (D E : List Nat) (T : Tree)
    (h : ∀ x, x ∈ leaves T → D.contains x = E.contains x) :
    rootedSpan D T = rootedSpan E T := by
  induction T with
  | leaf x => simp only [rootedSpan,h x (by simp [leaves])]
  | node l r ihl ihr =>
    have hl := ihl (fun x hx => h x (List.mem_append_left _ hx))
    have hr := ihr (fun x hx => h x (List.mem_append_right _ hx))
    simp [rootedSpan,hl,hr]

theorem minimalVertices_ext (D E : List Nat) (T : Tree)
    (h : ∀ x, x ∈ leaves T → D.contains x = E.contains x) :
    minimalVertices D T = minimalVertices E T := by
  induction T with
  | leaf x => simp only [minimalVertices,h x (by simp [leaves])]
  | node l r ihl ihr =>
    have hle := fun x hx => h x (List.mem_append_left (leaves r) hx)
    have hre := fun x hx => h x (List.mem_append_right (leaves l) hx)
    simp [minimalVertices, rootedSpan_ext D E l hle, rootedSpan_ext D E r hre,
      ihl hle, ihr hre]

theorem subtree_selected_span {D : List Nat} {T : Tree} {q : RMAF.Vertex} {x : Nat}
    (hx : x ∈ subtreeLabels T q) (hD : x ∈ D) : q ∈ rootedSpan D T := by
  induction q generalizing T with
  | nil => exact (rootedSpan_root D T).2 (by
      have he := rootspan_nonempty hx hD
      intro hn
      simp [hn] at he)
  | cons s q ih =>
    cases T with
    | leaf y => simp [subtreeLabels] at hx
    | node l r => exact (rootedSpan_child D l r s q).2 (ih hx)

/-- No selected original label lies below a directed child edge leaving the
original a--b path. The quantified child is nonroot; no edge at rho is added. -/
def PendantExcluded (D : List Nat) (a b : Nat) (S : Tree) : Prop :=
  ∀ q : RMAF.Vertex, q ≠ [] → q.dropLast ∈ minimalVertices [a,b] S →
    q ∉ minimalVertices [a,b] S → ∀ x, x ∈ subtreeLabels S q → x ∉ D

theorem fork_excluded {D : List Nat} {l r : Tree} {a b : Nat}
    (hl : restrict D l = some (.leaf a)) (hr : restrict D r = some (.leaf b)) :
    PendantExcluded D a b (.node l r) := by
  have ha := (restrict_mem hl a).1 (by simp [leaves])
  have hb := (restrict_mem hr b).1 (by simp [leaves])
  have hext : rootedSpan D (.node l r) = rootedSpan [a,b] (.node l r) := by
    apply rootedSpan_ext
    intro x hx
    have hm : x ∈ D ↔ x = a ∨ x = b := by
      constructor
      · intro hD
        rcases List.mem_append.1 hx with hxl | hxr
        · exact Or.inl (by simpa [leaves] using (restrict_mem hl x).2 ⟨hxl,hD⟩)
        · exact Or.inr (by simpa [leaves] using (restrict_mem hr x).2 ⟨hxr,hD⟩)
      · rintro (rfl | rfl)
        · exact ha.2
        · exact hb.2
    cases hd : D.contains x <;> cases hp : ([a,b] : List Nat).contains x <;> simp_all
  have hL : (rootedSpan [a,b] l).isEmpty = false := rootspan_nonempty ha.1 (by simp)
  have hR : (rootedSpan [a,b] r).isEmpty = false := rootspan_nonempty hb.1 (by simp)
  have heq : minimalVertices [a,b] (.node l r) = rootedSpan D (.node l r) := by
    rw [hext]
    simp [minimalVertices,rootedSpan,hL,hR]
  intro q hq hp hn x hx hD
  exact hn (heq ▸ subtree_selected_span hx hD)

theorem pairSpan_left {l r : Tree} {a b : Nat}
    (hal : a ∈ leaves l) (hbr : b ∈ leaves l)
    (har : a ∉ leaves r) (hbr' : b ∉ leaves r) :
    minimalVertices [a,b] (.node l r) = prependSide false (minimalVertices [a,b] l) := by
  have hL : (rootedSpan [a,b] l).isEmpty = false := rootspan_nonempty hal (by simp)
  have hR : rootedSpan [a,b] r = [] := rootspan_empty (by intro x hx; simpa using ⟨fun he => har (he ▸ hx),fun he => hbr' (he ▸ hx)⟩)
  simp [minimalVertices,hL,hR]

theorem pairSpan_right {l r : Tree} {a b : Nat}
    (hal : a ∈ leaves r) (hbr : b ∈ leaves r)
    (har : a ∉ leaves l) (hbr' : b ∉ leaves l) :
    minimalVertices [a,b] (.node l r) = prependSide true (minimalVertices [a,b] r) := by
  have hL : rootedSpan [a,b] l = [] := rootspan_empty (by intro x hx; simpa using ⟨fun he => har (he ▸ hx),fun he => hbr' (he ▸ hx)⟩)
  simp [minimalVertices,hL]

theorem prunedCherry_excluded {D a b S} (hc : PrunedCherry D a b S) :
    PendantExcluded D a b S := by
  induction hc with
  | fork hl hr => exact fork_excluded hl hr
  | @forkSwap l r hl hr =>
    have hh := fork_excluded hl hr
    have he := minimalVertices_ext [b,a] [a,b] (Tree.node l r)
      (by intro x hx; simp [List.contains_cons,Bool.or_comm])
    simpa only [PendantExcluded,he] using hh
  | @left l r hc ha hb ih =>
    have hm := pairSpan_left (prunedCherry_labels hc).1 (prunedCherry_labels hc).2 ha hb
    intro q hq hp hn x hx hD
    cases q with
    | nil => exact hq rfl
    | cons s q =>
      cases q with
      | nil => simp [hm,prependSide] at hp
      | cons c q =>
        cases s
        · have hp' : (c :: q).dropLast ∈ minimalVertices [a,b] l := by simpa [hm,prependSide] using hp
          have hn' : c :: q ∉ minimalVertices [a,b] l := by simpa [hm,prependSide] using hn
          exact ih (c :: q) (by simp) hp' hn' x hx hD
        · simp [hm,prependSide] at hp
  | @right l r hc ha hb ih =>
    have hm := pairSpan_right (prunedCherry_labels hc).1 (prunedCherry_labels hc).2 ha hb
    intro q hq hp hn x hx hD
    cases q with
    | nil => exact hq rfl
    | cons s q =>
      cases q with
      | nil => simp [hm,prependSide] at hp
      | cons c q =>
        cases s
        · simp [hm,prependSide] at hp
        · have hp' : (c :: q).dropLast ∈ minimalVertices [a,b] r := by simpa [hm,prependSide] using hp
          have hn' : c :: q ∉ minimalVertices [a,b] r := by simpa [hm,prependSide] using hn
          exact ih (c :: q) (by simp) hp' hn' x hx hD

/-- Actual restriction/RootedIso delivers the original-source pendant exclusion. -/
theorem original_common_block_excluded {T S : Tree} {F : List (List Nat)}
    (hn : (leaves S).Nodup) (ha : agreement T S F = true) {p : RMAF.Vertex} {a b : Nat}
    (hc : CherryAt T p a b) {B : List Nat} (hB : B ∈ F) (haB : a ∈ B) (hbB : b ∈ B) :
    PendantExcluded B a b S := by
  obtain ⟨U,hU,hcU⟩ := restrict_cherry_from_agreement ha hc hB haB hbB
  exact prunedCherry_excluded (prunedCherry_of_restrict hn hU hcU)
end Universal233.HardParent
