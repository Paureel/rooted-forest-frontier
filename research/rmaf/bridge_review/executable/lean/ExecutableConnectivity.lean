import RMAF
import GraphRegion

/-! Connectivity of the existing executable extractor. The RMAF definitions
are imported unchanged. No convexity, ancestry, or connectivity premise is
assumed for the extractor. Leastness and label interpretation are not claimed. -/
namespace ExecutableBridge
open RMAF BridgeReview

abbrev Connected (vs : List Vertex) : Prop :=
  ∀ u, u ∈ vs → ∀ v, v ∈ vs → Walk (fun x => x ∈ vs) u v

theorem adj_symmetric {u v : Vertex} (h : Adj u v) : Adj v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem walk_trans {P : Vertex → Prop} {u v w : Vertex}
    (a : Walk P u v) (b : Walk P v w) : Walk P u w := by
  induction b with
  | refl _ => exact a
  | step _ he hm ih => exact .step ih he hm

theorem walk_reverse {P : Vertex → Prop} {u v : Vertex}
    (w : Walk P u v) : Walk P v u := by
  induction w with
  | refl h => exact .refl h
  | step w he hm ih =>
    exact walk_trans (.step (.refl hm) (adj_symmetric he) w.finish) ih

theorem walk_map {P Q : Vertex → Prop} {u v : Vertex} (f : Vertex → Vertex)
    (hedge : ∀ a b, Adj a b → Adj (f a) (f b))
    (hmem : ∀ a, P a → Q (f a)) (w : Walk P u v) : Walk Q (f u) (f v) := by
  induction w with
  | refl h => exact .refl (hmem _ h)
  | step _ he hm ih => exact .step ih (hedge _ _ he) (hmem _ hm)

theorem adj_prepend (side : Bool) {u v : Vertex} (h : Adj u v) :
    Adj (side :: u) (side :: v) := by
  rcases h with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact Or.inr ⟨b, rfl⟩

theorem connected_prepend (side : Bool) (vs : List Vertex) (h : Connected vs) :
    Connected (prependSide side vs) := by
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
  exact walk_map (fun x => side :: x) (fun _ _ he => adj_prepend side he)
    (by intro x hx; simp [prependSide, hx]) (h a ha b hb)

def joinSpan (ls rs : List Vertex) : List Vertex :=
  [] :: (prependSide false ls ++ prependSide true rs)

theorem join_left_walk (ls rs : List Vertex) {v : Vertex}
    (w : Walk (fun x => x ∈ ls) [] v) :
    Walk (fun x => x ∈ joinSpan ls rs) [] (false :: v) := by
  have lifted := walk_map (Q := fun x => x ∈ joinSpan ls rs) (fun x => false :: x)
    (fun _ _ he => adj_prepend false he) (by intro x hx; simp [joinSpan, prependSide, hx]) w
  exact walk_trans (.step (.refl (by simp [joinSpan]))
    (Or.inl ⟨false, rfl⟩) lifted.start) lifted

theorem join_right_walk (ls rs : List Vertex) {v : Vertex}
    (w : Walk (fun x => x ∈ rs) [] v) :
    Walk (fun x => x ∈ joinSpan ls rs) [] (true :: v) := by
  have lifted := walk_map (Q := fun x => x ∈ joinSpan ls rs) (fun x => true :: x)
    (fun _ _ he => adj_prepend true he) (by intro x hx; simp [joinSpan, prependSide, hx]) w
  exact walk_trans (.step (.refl (by simp [joinSpan]))
    (Or.inl ⟨true, rfl⟩) lifted.start) lifted

/-- Every vertex emitted by rootedSpan is joined to its input root using only
emitted vertices and one-bit graph edges. Empty spans need no witness. -/
theorem rootedSpan_walk (selected : List Nat) (t : Tree) :
    ∀ v, v ∈ rootedSpan selected t →
      Walk (fun x => x ∈ rootedSpan selected t) [] v := by
  induction t with
  | leaf x =>
    intro v hv
    by_cases hx : x ∈ selected
    · simp [rootedSpan, hx] at hv
      subst v
      exact .refl (by simp [rootedSpan, hx])
    · simp [rootedSpan, hx] at hv
  | node l r ihl ihr =>
    intro v hv
    by_cases hn : ((rootedSpan selected l).isEmpty && (rootedSpan selected r).isEmpty) = true
    · simp [rootedSpan, hn] at hv
    · have hs : rootedSpan selected (.node l r) =
          joinSpan (rootedSpan selected l) (rootedSpan selected r) := by
        simp [rootedSpan, hn, joinSpan]
      rw [hs] at hv ⊢
      rcases List.mem_cons.mp hv with hv | hv
      · subst v
        exact .refl (by simp [joinSpan])
      · rcases List.mem_append.mp hv with hl | hr
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hl
          exact join_left_walk _ _ (ihl w hw)
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
          exact join_right_walk _ _ (ihr w hw)

theorem rootedSpan_connected (selected : List Nat) (t : Tree) :
    Connected (rootedSpan selected t) := by
  intro u hu v hv
  exact walk_trans (walk_reverse (rootedSpan_walk selected t u hu))
    (rootedSpan_walk selected t v hv)

/-- The actual minimalVertices output is connected. The proof follows its
three branches, including suppression of the unused initial root path. -/
theorem minimalVertices_connected (selected : List Nat) (t : Tree) :
    Connected (minimalVertices selected t) := by
  induction t with
  | leaf x =>
    intro u hu v hv
    by_cases hx : x ∈ selected
    · simp [minimalVertices, hx] at hu hv
      subst u; subst v
      exact .refl (by simp [minimalVertices, hx])
    · simp [minimalVertices, hx] at hu
  | node l r ihl ihr =>
    by_cases hl : (rootedSpan selected l).isEmpty = true
    · simpa [minimalVertices, hl] using connected_prepend true _ ihr
    · by_cases hr : (rootedSpan selected r).isEmpty = true
      · simpa [minimalVertices, hl, hr] using connected_prepend false _ ihl
      · have hs : minimalVertices selected (.node l r) = rootedSpan selected (.node l r) := by
          simp [minimalVertices, rootedSpan, hl, hr]
        rw [hs]
        exact rootedSpan_connected selected (.node l r)

theorem isEmpty_false_of_nonempty {α : Type} (xs : List α) (h : xs ≠ []) :
    xs.isEmpty = false := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons _ _ => rfl

/-- Actual occurrence of a selected label suffices; no unique-label assumption
is needed for this connectivity/nonemptiness statement. -/
theorem rootedSpan_nonempty_of_leaf (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) : rootedSpan selected t ≠ [] := by
  induction t with
  | leaf a =>
    have hxa : x = a := by simpa [leaves] using hx
    subst a
    simp [rootedSpan, hs]
  | node l r ihl ihr =>
    rcases List.mem_append.mp hx with hl | hr
    · have h := isEmpty_false_of_nonempty _ (ihl hl)
      simp [rootedSpan, h]
    · have h := isEmpty_false_of_nonempty _ (ihr hr)
      simp [rootedSpan, h]

theorem minimalVertices_nonempty_of_leaf (selected : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : x ∈ selected) : minimalVertices selected t ≠ [] := by
  induction t with
  | leaf a =>
    have hxa : x = a := by simpa [leaves] using hx
    subst a
    simp [minimalVertices, hs]
  | node l r ihl ihr =>
    rcases List.mem_append.mp hx with hl | hr
    · have hls := isEmpty_false_of_nonempty _ (rootedSpan_nonempty_of_leaf selected l x hl hs)
      by_cases hrs : (rootedSpan selected r).isEmpty = true
      · simpa [minimalVertices, hls, hrs, prependSide] using ihl hl
      · simp [minimalVertices, hls, hrs]
    · have hrs := isEmpty_false_of_nonempty _ (rootedSpan_nonempty_of_leaf selected r x hr hs)
      by_cases hls : (rootedSpan selected l).isEmpty = true
      · simpa [minimalVertices, hls, prependSide] using ihr hr
      · simp [minimalVertices, hls, hrs]

/-- The existing extractor now supplies its graph-connected support directly. -/
def extractedSupport (selected : List Nat) (t : Tree)
    (hne : minimalVertices selected t ≠ []) : ConnectedSupport where
  first := (minimalVertices selected t).head hne
  rest := (minimalVertices selected t).tail
  connected := by
    change Connected ((minimalVertices selected t).head hne :: (minimalVertices selected t).tail)
    rw [List.cons_head_tail hne]
    exact minimalVertices_connected selected t

theorem extractedSupport_exact (selected : List Nat) (t : Tree)
    (hne : minimalVertices selected t ≠ []) :
    (extractedSupport selected t hne).first :: (extractedSupport selected t hne).rest =
      minimalVertices selected t := List.cons_head_tail hne

noncomputable def extractedRegion (selected : List Nat) (t : Tree)
    (hne : minimalVertices selected t ≠ []) : PureBridge.RootedRegion :=
  (extractedSupport selected t hne).toRootedRegion

theorem extractedRegion_exact (selected : List Nat) (t : Tree)
    (hne : minimalVertices selected t ≠ []) (v : Vertex) :
    (extractedRegion selected t hne).member v ↔ v ∈ minimalVertices selected t := by
  change v ∈ (extractedSupport selected t hne).first :: (extractedSupport selected t hne).rest ↔ _
  rw [extractedSupport_exact]

/-- Direct composition with the original consumer, with precisely the original
extractor's membership and the printed depth/overlap hypotheses. -/
theorem deepest_extracted_root_in_neighbor (sa sb : List Nat) (ta tb : Tree)
    (ha : minimalVertices sa ta ≠ []) (hb : minimalVertices sb tb ≠ [])
    (hdepth : (extractedSupport sb tb hb).root.length ≤ (extractedSupport sa ta ha).root.length)
    (hoverlap : ∃ z, z ∈ minimalVertices sa ta ∧ z ∈ minimalVertices sb tb) :
    (extractedSupport sa ta ha).root ∈ minimalVertices sb tb := by
  have h := ConnectedSupport.deepest_graph_root_in_neighbor
    (extractedSupport sa ta ha) (extractedSupport sb tb hb) hdepth
    (by simpa only [extractedSupport_exact] using hoverlap)
  simpa only [extractedSupport_exact] using h

#print axioms adj_symmetric
#print axioms walk_trans
#print axioms walk_reverse
#print axioms walk_map
#print axioms adj_prepend
#print axioms connected_prepend
#print axioms join_left_walk
#print axioms join_right_walk
#print axioms rootedSpan_walk
#print axioms rootedSpan_connected
#print axioms minimalVertices_connected
#print axioms isEmpty_false_of_nonempty
#print axioms rootedSpan_nonempty_of_leaf
#print axioms minimalVertices_nonempty_of_leaf
#print axioms extractedSupport
#print axioms extractedSupport_exact
#print axioms extractedRegion
#print axioms extractedRegion_exact
#print axioms deepest_extracted_root_in_neighbor
end ExecutableBridge
