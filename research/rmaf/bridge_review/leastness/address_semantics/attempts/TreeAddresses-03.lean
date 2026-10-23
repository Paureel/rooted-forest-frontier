import RMAF

/-! Actual node and selected leaf occurrences in the unchanged executable tree.
This module proves semantic vocabulary only; it does not import any extraction,
connectivity, prefix-hull, or leastness result. -/

namespace LeastEmbedding
open RMAF

def vertices : Tree → List Vertex
  | .leaf _ => [[]]
  | .node l r => [] :: (prependSide false (vertices l) ++ prependSide true (vertices r))

def terminals (selected : List Nat) : Tree → List Vertex
  | .leaf x => if selected.contains x then [[]] else []
  | .node l r => prependSide false (terminals selected l) ++
      prependSide true (terminals selected r)

/-- The root is an actual vertex of every tree; child occurrences retain sides. -/
inductive ValidVertex : Tree → Vertex → Prop where
  | root (t : Tree) : ValidVertex t []
  | left {l r : Tree} {v : Vertex} : ValidVertex l v → ValidVertex (.node l r) (false :: v)
  | right {l r : Tree} {v : Vertex} : ValidVertex r v → ValidVertex (.node l r) (true :: v)

/-- A leaf occurrence includes its actual address, not merely its label. -/
inductive LeafOccurrence : Tree → Vertex → Nat → Prop where
  | leaf (x : Nat) : LeafOccurrence (.leaf x) [] x
  | left {l r : Tree} {v : Vertex} {x : Nat} :
      LeafOccurrence l v x → LeafOccurrence (.node l r) (false :: v) x
  | right {l r : Tree} {v : Vertex} {x : Nat} :
      LeafOccurrence r v x → LeafOccurrence (.node l r) (true :: v) x

theorem mem_vertices_iff {t : Tree} {v : Vertex} :
    v ∈ vertices t ↔ ValidVertex t v := by
  induction t generalizing v with
  | leaf x =>
      constructor
      · intro h
        have hv : v = [] := by simpa [vertices] using h
        subst v
        exact .root _
      · intro h
        cases h
        simp [vertices]
  | node l r ihl ihr =>
      constructor
      · intro h
        rcases List.mem_cons.mp h with hroot | hchild
        · subst v
          exact .root _
        · rcases List.mem_append.mp hchild with hl | hr
          · rcases List.mem_map.mp hl with ⟨w, hw, rfl⟩
            exact .left (ihl.mp hw)
          · rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
            exact .right (ihr.mp hw)
      · intro h
        cases h with
        | root => simp [vertices]
        | left hv =>
            exact List.mem_cons_of_mem _ (List.mem_append_left _
              (List.mem_map.mpr ⟨_, ihl.mpr hv, rfl⟩))
        | right hv =>
            exact List.mem_cons_of_mem _ (List.mem_append_right _
              (List.mem_map.mpr ⟨_, ihr.mpr hv, rfl⟩))

theorem mem_terminals_iff {selected : List Nat} {t : Tree} {v : Vertex} :
    v ∈ terminals selected t ↔ ∃ x, LeafOccurrence t v x ∧ x ∈ selected := by
  induction t generalizing v with
  | leaf x =>
      constructor
      · intro h
        have hx : x ∈ selected := by
          by_cases hx : x ∈ selected
          · exact hx
          · simp [terminals, hx] at h
        have hv : v = [] := by simpa [terminals, hx] using h
        subst v
        exact ⟨x, .leaf x, hx⟩
      · rintro ⟨y, ho, hy⟩
        cases ho
        simp [terminals, hy]
  | node l r ihl ihr =>
      constructor
      · intro h
        rcases List.mem_append.mp h with hl | hr
        · rcases List.mem_map.mp hl with ⟨w, hw, rfl⟩
          rcases ihl.mp hw with ⟨x, ho, hx⟩
          exact ⟨x, .left ho, hx⟩
        · rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
          rcases ihr.mp hw with ⟨x, ho, hx⟩
          exact ⟨x, .right ho, hx⟩
      · rintro ⟨x, ho, hx⟩
        cases ho with
        | left hv =>
            exact List.mem_append_left _
              (List.mem_map.mpr ⟨_, ihl.mpr ⟨x, hv, hx⟩, rfl⟩)
        | right hv =>
            exact List.mem_append_right _
              (List.mem_map.mpr ⟨_, ihr.mpr ⟨x, hv, hx⟩, rfl⟩)

theorem LeafOccurrence.valid {t : Tree} {v : Vertex} {x : Nat}
    (h : LeafOccurrence t v x) : ValidVertex t v := by
  induction h with
  | leaf x => exact .root _
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem LeafOccurrence.mem_leaves {t : Tree} {v : Vertex} {x : Nat}
    (h : LeafOccurrence t v x) : x ∈ leaves t := by
  induction h with
  | leaf x => simp [leaves]
  | left _ ih => exact List.mem_append_left _ ih
  | right _ ih => exact List.mem_append_right _ ih

theorem mem_leaves_iff_occurrence {t : Tree} {x : Nat} :
    x ∈ leaves t ↔ ∃ v, LeafOccurrence t v x := by
  constructor
  · intro h
    induction t with
    | leaf y =>
        have hxy : x = y := by simpa [leaves] using h
        subst y
        exact ⟨[], .leaf x⟩
    | node l r ihl ihr =>
        rcases List.mem_append.mp h with hl | hr
        · rcases ihl hl with ⟨v, hv⟩
          exact ⟨false :: v, .left hv⟩
        · rcases ihr hr with ⟨v, hv⟩
          exact ⟨true :: v, .right hv⟩
  · rintro ⟨v, hv⟩
    exact hv.mem_leaves

theorem LeafOccurrence.label_unique {t : Tree} {v : Vertex} {x y : Nat}
    (hx : LeafOccurrence t v x) (hy : LeafOccurrence t v y) : x = y := by
  induction hx generalizing y with
  | leaf x => cases hy; rfl
  | left hx ih => cases hy with | left hy => exact ih hy
  | right hx ih => cases hy with | right hy => exact ih hy

theorem terminals_subset_vertices {selected : List Nat} {t : Tree} {v : Vertex}
    (h : v ∈ terminals selected t) : v ∈ vertices t := by
  rcases mem_terminals_iff.mp h with ⟨x, ho, _⟩
  exact mem_vertices_iff.mpr ho.valid

theorem terminal_nonempty {selected : List Nat} {t : Tree} {x : Nat}
    (hx : x ∈ leaves t) (hs : x ∈ selected) : terminals selected t ≠ [] := by
  rcases mem_leaves_iff_occurrence.mp hx with ⟨v, hv⟩
  have hm : v ∈ terminals selected t := mem_terminals_iff.mpr ⟨x, hv, hs⟩
  intro he
  simp [he] at hm

/-- Unique labels imply unique addresses. Repeated-label trees need not satisfy this. -/
theorem LeafOccurrence.address_unique {t : Tree} {v w : Vertex} {x : Nat}
    (hn : (leaves t).Nodup) (hv : LeafOccurrence t v x)
    (hw : LeafOccurrence t w x) : v = w := by
  induction t generalizing v w with
  | leaf y => cases hv; cases hw; rfl
  | node l r ihl ihr =>
      have hd := List.nodup_append.mp hn
      cases hv with
      | left hv =>
          cases hw with
          | left hw => exact congrArg (false :: ·) (ihl hd.1 hv hw)
          | right hw => exact False.elim (hd.2.2 x hv.mem_leaves x hw.mem_leaves rfl)
      | right hv =>
          cases hw with
          | left hw => exact False.elim (hd.2.2 x hw.mem_leaves x hv.mem_leaves rfl)
          | right hw => exact congrArg (true :: ·) (ihr hd.2.1 hv hw)

theorem unique_occurrence_of_nodup {t : Tree} {x : Nat}
    (hn : (leaves t).Nodup) (hx : x ∈ leaves t) :
    ∃ v, LeafOccurrence t v x ∧ ∀ w, LeafOccurrence t w x → w = v := by
  rcases mem_leaves_iff_occurrence.mp hx with ⟨v, hv⟩
  exact ⟨v, hv, fun _ hw => hw.address_unique hn hv⟩

theorem instance_left_nodup (i : Instance) : (leaves i.left).Nodup :=
  i.labels_left.nodup_iff.mpr List.nodup_range

theorem instance_right_nodup (i : Instance) : (leaves i.right).Nodup :=
  i.labels_right.nodup_iff.mpr List.nodup_range

theorem instance_left_mem_leaves_iff (i : Instance) (x : Nat) :
    x ∈ leaves i.left ↔ x < i.n :=
  i.labels_left.mem_iff.trans List.mem_range

theorem instance_right_mem_leaves_iff (i : Instance) (x : Nat) :
    x ∈ leaves i.right ↔ x < i.n :=
  i.labels_right.mem_iff.trans List.mem_range

theorem instance_left_unique_occurrence (i : Instance) {x : Nat} (hx : x < i.n) :
    ∃ v, LeafOccurrence i.left v x ∧ ∀ w, LeafOccurrence i.left w x → w = v :=
  unique_occurrence_of_nodup (instance_left_nodup i)
    ((instance_left_mem_leaves_iff i x).mpr hx)

theorem instance_right_unique_occurrence (i : Instance) {x : Nat} (hx : x < i.n) :
    ∃ v, LeafOccurrence i.right v x ∧ ∀ w, LeafOccurrence i.right w x → w = v :=
  unique_occurrence_of_nodup (instance_right_nodup i)
    ((instance_right_mem_leaves_iff i x).mpr hx)

theorem instance_left_occurrence_iff (i : Instance) (x : Nat) :
    (∃ v, LeafOccurrence i.left v x) ↔ x < i.n :=
  mem_leaves_iff_occurrence.symm.trans (instance_left_mem_leaves_iff i x)

theorem instance_right_occurrence_iff (i : Instance) (x : Nat) :
    (∃ v, LeafOccurrence i.right v x) ↔ x < i.n :=
  mem_leaves_iff_occurrence.symm.trans (instance_right_mem_leaves_iff i x)

end LeastEmbedding
