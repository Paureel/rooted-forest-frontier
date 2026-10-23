import Std

/-! Original-edge normalization: exact cut provenance, finite cost, and graph walks.
This file does NOT assert agreement-forest preservation or suppression transport.
A path is an actual edge-labelled walk; its edge predicate is explicit.
No cutsets are identified from equality of their labelled partitions. -/
namespace RootSafeOriginalEdges

variable {Edge Vertex Label : Type} [DecidableEq Edge]

def kept (cuts : List Edge) (onPath : Edge → Bool) : List Edge :=
  cuts.filter (fun e => !onPath e)

def removed (cuts : List Edge) (onPath : Edge → Bool) : List Edge :=
  cuts.filter onPath

def normalize (cuts : List Edge) (onPath : Edge → Bool)
    (parent : Option Edge) : List Edge :=
  if 2 ≤ (removed cuts onPath).length then
    match parent with
    | none => kept cuts onPath
    | some e => (kept cuts onPath).insert e
  else kept cuts onPath

def Added (cuts : List Edge) (onPath : Edge → Bool)
    (parent : Option Edge) (e : Edge) : Prop :=
  2 ≤ (removed cuts onPath).length ∧ parent = some e

theorem normalize_mem (cuts : List Edge) (onPath : Edge → Bool)
    (parent : Option Edge) (e : Edge) :
    e ∈ normalize cuts onPath parent ↔
      (e ∈ cuts ∧ onPath e = false) ∨ Added cuts onPath parent e := by
  cases parent with
  | none => simp [normalize, Added, kept, List.mem_filter]
  | some p =>
    by_cases h : 2 ≤ (removed cuts onPath).length
    · simp only [normalize]
      simp only [h, ite_true]
      simp only [kept, List.mem_insert_iff, List.mem_filter,
        Added, h, true_and, Option.some.injEq]
      constructor
      · intro he
        rcases he with he | he
        · exact Or.inr he.symm
        · exact Or.inl (by simpa using he)
      · intro he
        rcases he with he | he
        · exact Or.inr (by simpa using he)
        · exact Or.inl he.symm
    · simp [normalize, Added, kept, List.mem_filter, h]

theorem original_edge_provenance (cuts : List Edge) (onPath : Edge → Bool)
    (parent : Option Edge) (original : Edge → Prop)
    (old : ∀ e ∈ cuts, original e)
    (hp : ∀ e, parent = some e → original e) :
    ∀ e ∈ normalize cuts onPath parent, original e := by
  intro e he
  rcases (normalize_mem cuts onPath parent e).mp he with h | h
  · exact old e h.1
  · exact hp e h.2

theorem restored_path_is_uncut (cuts : List Edge) (onPath : Edge → Bool)
    (parent : Option Edge)
    (parent_off_path : ∀ e, parent = some e → onPath e = false) :
    ∀ e, onPath e = true → e ∉ normalize cuts onPath parent := by
  intro e hpath hcut
  rcases (normalize_mem cuts onPath parent e).mp hcut with h | h
  · simp [hpath] at h
  · have hfalse := parent_off_path e h.2
    simp [hpath] at hfalse

theorem protected_cuts_retained (cuts required : List Edge)
    (onPath : Edge → Bool) (parent : Option Edge)
    (subset : ∀ e ∈ required, e ∈ cuts)
    (disjoint : ∀ e ∈ required, onPath e = false) :
    ∀ e ∈ required, e ∈ normalize cuts onPath parent := by
  intro e he
  exact (normalize_mem cuts onPath parent e).mpr (Or.inl ⟨subset e he, disjoint e he⟩)

theorem root_normalization_exact (cuts : List Edge) (onPath : Edge → Bool) :
    normalize cuts onPath none = kept cuts onPath := by
  simp [normalize]

omit [DecidableEq Edge] in
theorem kept_removed_length (cuts : List Edge) (onPath : Edge → Bool) :
    (kept cuts onPath).length + (removed cuts onPath).length = cuts.length := by
  induction cuts with
  | nil => simp [kept, removed]
  | cons e es ih =>
    cases h : onPath e <;>
      simp [kept, removed, h] at * <;> omega

theorem normalized_cost_le (cuts : List Edge) (onPath : Edge → Bool)
    (parent : Option Edge) :
    (normalize cuts onPath parent).length ≤ cuts.length := by
  have hsum := kept_removed_length cuts onPath
  unfold normalize
  split
  · cases parent with
    | none =>
      change (kept cuts onPath).length ≤ cuts.length
      omega
    | some p =>
      change ((kept cuts onPath).insert p).length ≤ cuts.length
      have hins : ((kept cuts onPath).insert p).length ≤
          (kept cuts onPath).length + 1 := by
        rw [List.length_insert]
        split <;> omega
      omega
  · omega

theorem root_cost_exact (cuts : List Edge) (onPath : Edge → Bool) :
    (normalize cuts onPath none).length + (removed cuts onPath).length =
      cuts.length := by
  rw [root_normalization_exact]
  exact kept_removed_length cuts onPath

theorem normalized_nodup (cuts : List Edge) (onPath : Edge → Bool)
    (parent : Option Edge) (h : cuts.Nodup) :
    (normalize cuts onPath parent).Nodup := by
  have hk : (kept cuts onPath).Nodup := List.Pairwise.filter _ h
  unfold normalize
  split
  · cases parent with
    | none => exact hk
    | some p =>
      change ((kept cuts onPath).insert p).Nodup
      by_cases hm : p ∈ kept cuts onPath
      · simpa [List.insert, hm] using hk
      · simp [List.insert, hm, List.nodup_cons, hk]
  · exact hk

/-- Every traversed edge retains its original ID and its endpoints. -/
inductive Walk (inc : Edge → Vertex → Vertex → Prop) (live : Edge → Prop) :
    Vertex → Vertex → Prop where
  | refl (v : Vertex) : Walk inc live v v
  | step {u v w : Vertex} {e : Edge} :
      inc e u v → live e → Walk inc live v w → Walk inc live u w

namespace Walk

omit [DecidableEq Edge] in
theorem mono {inc : Edge → Vertex → Vertex → Prop} {p q : Edge → Prop}
    {u v : Vertex} (h : Walk inc p u v) (hpq : ∀ e, p e → q e) :
    Walk inc q u v := by
  induction h with
  | refl w => exact .refl w
  | @step u v w e hinc hp htail ih => exact .step hinc (hpq e hp) ih

omit [DecidableEq Edge] in
theorem trans {inc : Edge → Vertex → Vertex → Prop} {p : Edge → Prop}
    {u v w : Vertex} (h : Walk inc p u v) (k : Walk inc p v w) :
    Walk inc p u w := by
  induction h with
  | refl _ => exact k
  | step hi hp _ ih => exact .step hi hp (ih k)

omit [DecidableEq Edge] in
theorem symm {inc : Edge → Vertex → Vertex → Prop} {p : Edge → Prop}
    (hs : ∀ e u v, inc e u v → inc e v u)
    {u v : Vertex} (h : Walk inc p u v) : Walk inc p v u := by
  induction h with
  | refl w => exact .refl w
  | @step u v w e hi hp _ ih =>
    exact ih.trans (.step (hs e u v hi) hp (.refl u))

omit [DecidableEq Edge] in
/-- A graph component cannot leave a region if every live edge stays in it. -/
theorem confined {inc : Edge → Vertex → Vertex → Prop} {p : Edge → Prop}
    (inside : Vertex → Prop)
    (closed : ∀ e u v, inc e u v → p e → inside u → inside v)
    {u v : Vertex} (h : Walk inc p u v) (hu : inside u) : inside v := by
  induction h with
  | refl _ => exact hu
  | @step u v w e hi hp _ ih => exact ih (closed e u v hi hp hu)
end Walk

theorem endpoint_path_restored (inc : Edge → Vertex → Vertex → Prop)
    (cuts : List Edge) (onPath : Edge → Bool) (parent : Option Edge)
    (parent_off_path : ∀ e, parent = some e → onPath e = false)
    {a c : Vertex} (path : Walk inc (fun e => onPath e = true) a c) :
    Walk inc (fun e => e ∉ normalize cuts onPath parent) a c :=
  path.mono (restored_path_is_uncut cuts onPath parent parent_off_path)

theorem old_walk_avoiding_added_survives (inc : Edge → Vertex → Vertex → Prop)
    (cuts : List Edge) (onPath : Edge → Bool) (parent : Option Edge)
    {u v : Vertex}
    (h : Walk inc (fun e => e ∉ cuts ∧ ¬ Added cuts onPath parent e) u v) :
    Walk inc (fun e => e ∉ normalize cuts onPath parent) u v := by
  apply h.mono
  intro e he hn
  rcases (normalize_mem cuts onPath parent e).mp hn with hk | ha
  · exact he.1 hk.1
  · exact he.2 ha

/-- At a component root there is no new cut: every old connection survives. -/
theorem root_old_walk_survives (inc : Edge → Vertex → Vertex → Prop)
    (cuts : List Edge) (onPath : Edge → Bool) {u v : Vertex}
    (h : Walk inc (fun e => e ∉ cuts) u v) :
    Walk inc (fun e => e ∉ normalize cuts onPath none) u v := by
  apply h.mono
  intro e he hn
  rcases (normalize_mem cuts onPath none e).mp hn with hk | ha
  · exact he hk.1
  · simp [Added] at ha

/-- The corridor component is isolated when its only outgoing edges are
required pendant cuts or the explicitly added parent cut. This holds at a
root with no parent as well as in the >=2 non-root branch. -/
theorem normalized_component_isolated
    (inc : Edge → Vertex → Vertex → Prop)
    (cuts required : List Edge) (onPath : Edge → Bool) (parent : Option Edge)
    (inside : Vertex → Prop)
    (required_subset : ∀ e ∈ required, e ∈ cuts)
    (required_off_path : ∀ e ∈ required, onPath e = false)
    (boundary : ∀ e u v, inc e u v → inside u → ¬ inside v →
      e ∈ required ∨ Added cuts onPath parent e)
    {u v : Vertex} (hu : inside u)
    (h : Walk inc (fun e => e ∉ normalize cuts onPath parent) u v) :
    inside v := by
  apply h.confined inside _ hu
  intro e x y hi hl hx
  by_cases hy : inside y
  · exact hy
  · rcases boundary e x y hi hx hy with hr | ha
    · exact False.elim (hl (protected_cuts_retained cuts required onPath parent
          required_subset required_off_path e hr))
    · exact False.elim (hl ((normalize_mem cuts onPath parent e).mpr (Or.inr ha)))

/-- Nonempty root-fragment witnesses join after restoring the original path.
The fragment walks avoid the optional added parent edge explicitly. -/
theorem anchored_labels_join
    (inc : Edge → Vertex → Vertex → Prop)
    (symmetric : ∀ e u v, inc e u v → inc e v u)
    (cuts : List Edge) (onPath : Edge → Bool) (parent : Option Edge)
    (parent_off_path : ∀ e, parent = some e → onPath e = false)
    (label : Vertex → Option Label) {a c va vc : Vertex} {la lc : Label}
    (label_a : label va = some la) (label_c : label vc = some lc)
    (path : Walk inc (fun e => onPath e = true) a c)
    (anchor_a : Walk inc (fun e => e ∉ cuts ∧ ¬ Added cuts onPath parent e) a va)
    (anchor_c : Walk inc (fun e => e ∉ cuts ∧ ¬ Added cuts onPath parent e) c vc) :
    label va = some la ∧ label vc = some lc ∧
      Walk inc (fun e => e ∉ normalize cuts onPath parent) va vc := by
  have ha := old_walk_avoiding_added_survives inc cuts onPath parent anchor_a
  have hc := old_walk_avoiding_added_survives inc cuts onPath parent anchor_c
  have hp := endpoint_path_restored inc cuts onPath parent parent_off_path path
  exact ⟨label_a, label_c, (ha.symm symmetric).trans (hp.trans hc)⟩

/-- Full normalization refines a partial-restoration target only if that
partial target also contains every parent cut added by full normalization.
This is an inclusion of original edge IDs, not equality of yielded forests. -/
theorem full_to_partial_inclusion
    (cuts : List Edge) (onPath : Edge → Bool) (parent : Option Edge)
    (restorePart target : Edge → Prop)
    (part_on_path : ∀ e, restorePart e → onPath e = true)
    (old_kept : ∀ e ∈ cuts, ¬ restorePart e → target e)
    (parent_kept : ∀ e, Added cuts onPath parent e → target e) :
    ∀ e ∈ normalize cuts onPath parent, target e := by
  intro e he
  rcases (normalize_mem cuts onPath parent e).mp he with hk | ha
  · apply old_kept e hk.1
    intro hd
    have ht := part_on_path e hd
    simp [ht] at hk
  · exact parent_kept e ha

#print axioms normalize_mem
#print axioms original_edge_provenance
#print axioms restored_path_is_uncut
#print axioms protected_cuts_retained
#print axioms root_normalization_exact
#print axioms kept_removed_length
#print axioms normalized_cost_le
#print axioms root_cost_exact
#print axioms normalized_nodup
#print axioms Walk.mono
#print axioms Walk.trans
#print axioms Walk.symm
#print axioms Walk.confined
#print axioms endpoint_path_restored
#print axioms old_walk_avoiding_added_survives
#print axioms root_old_walk_survives
#print axioms normalized_component_isolated
#print axioms anchored_labels_join
#print axioms full_to_partial_inclusion
end RootSafeOriginalEdges
