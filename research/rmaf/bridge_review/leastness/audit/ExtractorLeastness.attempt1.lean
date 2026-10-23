import TreeAddresses
import ExecutableConnectivity

/-! Derivation of the actual extractor's ambient, terminal and leastness
properties. The exact source functions remain unchanged. No hull equality,
minimality, terminal preservation or ambient correctness is assumed. -/
namespace LeastEmbedding
open RMAF BridgeReview ExecutableBridge

theorem span_left_in_parent (selected : List Nat) (l r : Tree) (v : Vertex)
    (hv : v ∈ rootedSpan selected l) :
    false :: v ∈ rootedSpan selected (.node l r) := by
  have hn : rootedSpan selected l ≠ [] := by intro h; simp [h] at hv
  have he := isEmpty_false_of_nonempty _ hn
  simp [rootedSpan, he, prependSide, hv]

theorem span_right_in_parent (selected : List Nat) (l r : Tree) (v : Vertex)
    (hv : v ∈ rootedSpan selected r) :
    true :: v ∈ rootedSpan selected (.node l r) := by
  have hn : rootedSpan selected r ≠ [] := by intro h; simp [h] at hv
  have he := isEmpty_false_of_nonempty _ hn
  simp [rootedSpan, he, prependSide, hv]

/-- Every emitted rooted-span vertex has a selected leaf occurrence below it. -/
theorem span_terminal_descendant (selected : List Nat) (t : Tree) :
    ∀ v, v ∈ rootedSpan selected t →
      ∃ p, p ∈ terminals selected t ∧ v.IsPrefix p := by
  induction t with
  | leaf x =>
    intro v hv
    by_cases hx : x ∈ selected
    · simp [rootedSpan, hx] at hv
      subst v
      exact ⟨[], by simp [terminals, hx], List.prefix_refl []⟩
    · simp [rootedSpan, hx] at hv
  | node l r ihl ihr =>
    intro v hv
    by_cases hn : ((rootedSpan selected l).isEmpty && (rootedSpan selected r).isEmpty) = true
    · simp [rootedSpan, hn] at hv
    · have hs : rootedSpan selected (.node l r) =
          [] :: (prependSide false (rootedSpan selected l) ++ prependSide true (rootedSpan selected r)) := by
        simp [rootedSpan, hn]
      rw [hs] at hv
      rcases List.mem_cons.mp hv with hroot | hchild
      · subst v
        by_cases hl : rootedSpan selected l = []
        · have hr : rootedSpan selected r ≠ [] := by
            intro hr
            apply hn
            simp [hl, hr]
          obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil hr
          obtain ⟨p, hp, _⟩ := ihr w hw
          exact ⟨true :: p, by simp [terminals, prependSide, hp], List.nil_prefix _⟩
        · obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil hl
          obtain ⟨p, hp, _⟩ := ihl w hw
          exact ⟨false :: p, by simp [terminals, prependSide, hp], List.nil_prefix _⟩
      · rcases List.mem_append.mp hchild with hl | hr
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hl
          obtain ⟨p, hp, hwp⟩ := ihl w hw
          exact ⟨false :: p, by simp [terminals, prependSide, hp], by simpa using hwp⟩
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
          obtain ⟨p, hp, hwp⟩ := ihr w hw
          exact ⟨true :: p, by simp [terminals, prependSide, hp], by simpa using hwp⟩

theorem terminals_in_span (selected : List Nat) (t : Tree) :
    ∀ p, p ∈ terminals selected t → p ∈ rootedSpan selected t := by
  induction t with
  | leaf x => intro p hp; simpa [terminals, rootedSpan] using hp
  | node l r ihl ihr =>
    intro p hp
    rcases List.mem_append.mp hp with hl | hr
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hl
      exact span_left_in_parent selected l r w (ihl w hw)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      exact span_right_in_parent selected l r w (ihr w hw)

theorem span_in_vertices (selected : List Nat) (t : Tree) :
    ∀ v, v ∈ rootedSpan selected t → v ∈ vertices t := by
  induction t with
  | leaf x =>
    intro v hv
    by_cases hx : x ∈ selected
    · simpa [rootedSpan, vertices, hx] using hv
    · simp [rootedSpan, hx] at hv
  | node l r ihl ihr =>
    intro v hv
    by_cases hn : ((rootedSpan selected l).isEmpty && (rootedSpan selected r).isEmpty) = true
    · simp [rootedSpan, hn] at hv
    · have hs : rootedSpan selected (.node l r) =
          [] :: (prependSide false (rootedSpan selected l) ++ prependSide true (rootedSpan selected r)) := by
        simp [rootedSpan, hn]
      rw [hs] at hv
      rcases List.mem_cons.mp hv with hroot | hchild
      · subst v; simp [vertices]
      · rcases List.mem_append.mp hchild with hl | hr
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hl
          have h := ihl w hw
          simp [vertices, prependSide, h]
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
          have h := ihr w hw
          simp [vertices, prependSide, h]

theorem minimal_in_span (selected : List Nat) (t : Tree) :
    ∀ v, v ∈ minimalVertices selected t → v ∈ rootedSpan selected t := by
  induction t with
  | leaf x => intro v hv; simpa [minimalVertices, rootedSpan] using hv
  | node l r ihl ihr =>
    intro v hv
    by_cases hl : (rootedSpan selected l).isEmpty = true
    · simp only [minimalVertices, hl, ↓reduceIte] at hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      exact span_right_in_parent selected l r w (ihr w hw)
    · by_cases hr : (rootedSpan selected r).isEmpty = true
      · simp only [minimalVertices, hl, hr, ↓reduceIte] at hv
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        exact span_left_in_parent selected l r w (ihl w hw)
      · simpa [minimalVertices, rootedSpan, hl, hr] using hv

theorem minimal_terminal_descendant (selected : List Nat) (t : Tree) (v : Vertex)
    (hv : v ∈ minimalVertices selected t) :
    ∃ p, p ∈ terminals selected t ∧ v.IsPrefix p :=
  span_terminal_descendant selected t v (minimal_in_span selected t v hv)

theorem minimal_in_vertices (selected : List Nat) (t : Tree) (v : Vertex)
    (hv : v ∈ minimalVertices selected t) : v ∈ vertices t :=
  span_in_vertices selected t v (minimal_in_span selected t v hv)

/-- The initial-root suppression branches do not remove any selected terminal. -/
theorem terminals_in_minimal (selected : List Nat) (t : Tree) :
    ∀ p, p ∈ terminals selected t → p ∈ minimalVertices selected t := by
  induction t with
  | leaf x => intro p hp; simpa [terminals, minimalVertices] using hp
  | node l r ihl ihr =>
    intro p hp
    rcases List.mem_append.mp hp with hl | hr
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hl
      have hspan := terminals_in_span selected l w hw
      have hls : rootedSpan selected l ≠ [] := by intro h; simp [h] at hspan
      have hes := isEmpty_false_of_nonempty _ hls
      by_cases her : (rootedSpan selected r).isEmpty = true
      · simpa [minimalVertices, hes, her, prependSide] using ihl w hw
      · simp [minimalVertices, hes, her, prependSide, hspan]
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      have hspan := terminals_in_span selected r w hw
      have hrs : rootedSpan selected r ≠ [] := by intro h; simp [h] at hspan
      have hes := isEmpty_false_of_nonempty _ hrs
      by_cases hel : (rootedSpan selected l).isEmpty = true
      · simpa [minimalVertices, hel, prependSide] using ihr w hw
      · simp [minimalVertices, hel, hes, prependSide, hspan]

theorem common_prefix_across_children (a p q : Vertex)
    (hl : a.IsPrefix (false :: p)) (hr : a.IsPrefix (true :: q)) : a = [] := by
  cases a with
  | nil => rfl
  | cons b bs =>
    have hbf := (List.cons_prefix_cons.mp hl).1
    have hbt := (List.cons_prefix_cons.mp hr).1
    simp [hbf] at hbt

theorem common_prefix_lift (side : Bool) (ts : List Vertex) (v : Vertex)
    (hne : ∃ p, p ∈ ts)
    (hbelow : ∀ a, (∀ p, p ∈ ts → a.IsPrefix p) → a.IsPrefix v)
    (a : Vertex) (ha : ∀ p, p ∈ ts → a.IsPrefix (side :: p)) :
    a.IsPrefix (side :: v) := by
  cases a with
  | nil => exact List.nil_prefix _
  | cons b bs =>
    obtain ⟨p, hp⟩ := hne
    have hb : b = side := (List.cons_prefix_cons.mp (ha p hp)).1
    subst b
    exact List.cons_prefix_cons.mpr ⟨rfl,
      hbelow bs (fun p hp => (List.cons_prefix_cons.mp (ha p hp)).2)⟩

/-- Every common ancestor of the selected occurrences lies above every output
vertex. This derives the relevant LCA bound without assuming a hull equality. -/
theorem minimal_below_common_ancestor (selected : List Nat) (t : Tree) :
    ∀ a, (∀ p, p ∈ terminals selected t → a.IsPrefix p) →
      ∀ v, v ∈ minimalVertices selected t → a.IsPrefix v := by
  induction t with
  | leaf x =>
    intro a ha v hv
    exact ha v (by simpa [terminals, minimalVertices] using hv)
  | node l r ihl ihr =>
    intro a ha v hv
    by_cases hl : (rootedSpan selected l).isEmpty = true
    · simp only [minimalVertices, hl, ↓reduceIte] at hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      obtain ⟨p, hp, _⟩ := minimal_terminal_descendant selected r w hw
      exact common_prefix_lift true (terminals selected r) w ⟨p, hp⟩
        (fun b hb => ihr b hb w hw) a
        (by intro p hp; exact ha (true :: p) (by simp [terminals, prependSide, hp]))
    · by_cases hr : (rootedSpan selected r).isEmpty = true
      · simp only [minimalVertices, hl, hr, ↓reduceIte] at hv
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        obtain ⟨p, hp, _⟩ := minimal_terminal_descendant selected l w hw
        exact common_prefix_lift false (terminals selected l) w ⟨p, hp⟩
          (fun b hb => ihl b hb w hw) a
          (by intro p hp; exact ha (false :: p) (by simp [terminals, prependSide, hp]))
      · have hln : rootedSpan selected l ≠ [] := by intro h; simp [h] at hl
        have hrn : rootedSpan selected r ≠ [] := by intro h; simp [h] at hr
        obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil hln
        obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil hrn
        obtain ⟨p, hp, _⟩ := span_terminal_descendant selected l u hu
        obtain ⟨q, hq, _⟩ := span_terminal_descendant selected r w hw
        have hae := common_prefix_across_children a p q
          (ha (false :: p) (by simp [terminals, prependSide, hp]))
          (ha (true :: q) (by simp [terminals, prependSide, hq]))
        subst a
        exact List.nil_prefix _

/-- Any graph-connected support containing all selected occurrences contains
the full exact extractor output. No ambient or leastness premise is used. -/
theorem minimal_least (selected : List Nat) (t : Tree) (other : ConnectedSupport)
    (hterm : ∀ p, p ∈ terminals selected t → p ∈ other.first :: other.rest)
    (v : Vertex) (hv : v ∈ minimalVertices selected t) :
    v ∈ other.first :: other.rest := by
  obtain ⟨p, hp, hvp⟩ := minimal_terminal_descendant selected t v hv
  have hav : other.root.IsPrefix v := minimal_below_common_ancestor selected t other.root
    (fun q hq => other.toRootedRegion.below q (hterm q hq)) v hv
  exact other.toRootedRegion.convex v p hav hvp (hterm p hp)

#print axioms span_left_in_parent
#print axioms span_right_in_parent
#print axioms span_terminal_descendant
#print axioms terminals_in_span
#print axioms span_in_vertices
#print axioms minimal_in_span
#print axioms minimal_terminal_descendant
#print axioms minimal_in_vertices
#print axioms terminals_in_minimal
#print axioms common_prefix_across_children
#print axioms common_prefix_lift
#print axioms minimal_below_common_ancestor
#print axioms minimal_least
end LeastEmbedding
