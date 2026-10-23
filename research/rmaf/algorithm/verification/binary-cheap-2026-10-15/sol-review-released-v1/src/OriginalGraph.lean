import CutRecords

/-! One-shot original-graph residual semantics. Displayed edges are never
identified with single original edges. Every walk below uses CoreGraph.Adj. -/
namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration

abbrev Pre (p v : RMAF.Vertex) : Prop := p <+: v

def Live (cuts : List RMAF.Vertex) (v : RMAF.Vertex) : Prop :=
  ∀ p, p ∈ cuts → ¬ Pre p v

@[simp] theorem live_nil (v : RMAF.Vertex) : Live [] v := by
  intro p hp; cases hp

@[simp] theorem live_cons (p v : RMAF.Vertex) (cuts : List RMAF.Vertex) :
    Live (p :: cuts) v ↔ ¬ Pre p v ∧ Live cuts v := by
  simp [Live]

theorem live_ancestor {cuts : List RMAF.Vertex} {u v : RMAF.Vertex}
    (h : Live cuts v) (hp : Pre u v) : Live cuts u := by
  intro p hm hh
  exact h p hm (hh.trans hp)

theorem valid_ancestor {T : Tree} {u v : RMAF.Vertex}
    (hv : Valid T v) (h : Pre u v) : Valid T u := by
  obtain ⟨q,hq⟩ := h
  subst v
  induction u generalizing T with
  | nil => exact valid_root T
  | cons b u ih =>
    cases T with
    | leaf x => obtain ⟨s,hs⟩ := hv; simp [subtree] at hs
    | node l r => exact ih hv

theorem leaf_unique {T : Tree} (hn : (leaves T).Nodup) {a b : RMAF.Vertex} {x : Nat}
    (ha : LeafAt T a x) (hb : LeafAt T b x) : a = b :=
  VertexGeometry.singleton_selected_address_unique T x hn a b
    ((leafAt_selected T a x).1 ha) ((leafAt_selected T b x).1 hb)

theorem leaf_exists {T : Tree} {x : Nat} (hx : x ∈ leaves T) :
    ∃ a, LeafAt T a x := by
  obtain ⟨a,ha⟩ := (VertexGeometry.singleton_selected_exists T x).2 hx
  exact ⟨a,(leafAt_selected T a x).2 ha⟩

theorem leaves_nonempty (T : Tree) : leaves T ≠ [] := by
  induction T with
  | leaf x => simp [leaves]
  | node l r ihl ihr => simpa [leaves] using (fun he _ => ihl he)

theorem child_prefix_boundary {p u : RMAF.Vertex} {b : Bool}
    (h : Pre p (u ++ [b])) (hn : ¬ Pre p u) : p = u ++ [b] := by
  have hl : u.length < p.length := by
    apply Classical.byContradiction
    intro hc
    exact hn (List.prefix_of_prefix_length_le h (List.prefix_append u [b]) (by omega))
  exact h.eq_of_length (by have he := h.length_le; simp only [List.length_append,List.length_singleton] at *; omega)

/-- Literal removal of the two orientations of every recorded ORIGINAL edge. -/
def ResidualAdj (T : Tree) (cuts : List RMAF.Vertex) (u v : RMAF.Vertex) : Prop :=
  Adj T u v ∧ ∀ p, p ∈ cuts →
    ¬ (u = p.dropLast ∧ v = p) ∧ ¬ (v = p.dropLast ∧ u = p)

inductive ResidualWalk (T : Tree) (cuts : List RMAF.Vertex) :
    RMAF.Vertex → RMAF.Vertex → Prop
  | refl {v} : Valid T v → ResidualWalk T cuts v v
  | step {u v w} : ResidualAdj T cuts u v → ResidualWalk T cuts v w →
      ResidualWalk T cuts u w

theorem ResidualAdj.symm {T cuts u v} (h : ResidualAdj T cuts u v) :
    ResidualAdj T cuts v u := ⟨h.1.symm,fun p hp => (h.2 p hp).symm⟩

theorem ResidualWalk.start {T cuts u v} (h : ResidualWalk T cuts u v) : Valid T u := by
  cases h with
  | refl hv => exact hv
  | step he _ => exact he.1.1

theorem ResidualWalk.finish {T cuts u v} (h : ResidualWalk T cuts u v) : Valid T v := by
  induction h with
  | refl hv => exact hv
  | step he tail ih => exact ih

theorem ResidualWalk.trans {T cuts u v w} (h : ResidualWalk T cuts u v)
    (k : ResidualWalk T cuts v w) : ResidualWalk T cuts u w := by
  induction h with
  | refl => exact k
  | step he tail ih => exact .step he (ih k)

theorem ResidualWalk.reverse {T cuts u v} (h : ResidualWalk T cuts u v) :
    ResidualWalk T cuts v u := by
  induction h with
  | refl hv => exact .refl hv
  | step he tail ih => exact ih.trans (.step he.symm (.refl he.1.1))

/-- A residual original edge cannot cross either side of a recorded edge. -/
theorem residual_prefix_same {T cuts u v} (h : ResidualAdj T cuts u v)
    {p : RMAF.Vertex} (hp : p ∈ cuts) : Pre p u ↔ Pre p v := by
  have one : ∀ {u v : RMAF.Vertex}, ResidualAdj T cuts u v → Pre p v → Pre p u := by
    intro u v he hv
    apply Classical.byContradiction
    intro hu
    rcases he.1.2.2 with ⟨b,hb⟩ | ⟨b,hb⟩
    · subst v
      have ep := child_prefix_boundary hv hu
      have hd : (u ++ [b]).dropLast = u := by simp
      exact (he.2 p hp).1 ⟨by simpa [ep,hd],by simpa [ep]⟩
    · subst u
      exact hu (hv.trans (List.prefix_append v [b]))
  exact ⟨fun hu => one h.symm hu,fun hv => one h hv⟩

theorem residual_walk_prefix_same {T cuts u v} (h : ResidualWalk T cuts u v)
    {p : RMAF.Vertex} (hp : p ∈ cuts) : Pre p u ↔ Pre p v := by
  induction h with
  | refl => rfl
  | step he tail ih => exact (residual_prefix_same he hp).trans ih

/-- Region rooted at r: no cut strictly below r occurs on the path to v.
For r=[] this is exactly the live component when root cuts are forbidden. -/
def Region (cuts : List RMAF.Vertex) (r v : RMAF.Vertex) : Prop :=
  Pre r v ∧ ∀ p, p ∈ cuts → Pre p v → Pre p r

theorem region_ancestor {cuts r u v} (h : Region cuts r v)
    (hru : Pre r u) (huv : Pre u v) : Region cuts r u :=
  ⟨hru,fun p hp hpu => h.2 p hp (hpu.trans huv)⟩

theorem region_root (cuts : List RMAF.Vertex) (v : RMAF.Vertex)
    (hn : ∀ p, p ∈ cuts → p ≠ []) : Region cuts [] v ↔ Live cuts v := by
  constructor
  · intro h p hp hh
    exact hn p hp (List.prefix_nil.1 (h.2 p hp hh))
  · intro h
    exact ⟨List.nil_prefix,fun p hp hh => False.elim (h p hp hh)⟩

theorem region_down_edge {T cuts r u v} (hr : Region cuts r v)
    (hu : Pre r u) (hv : Valid T v) (b : Bool) (he : v = u ++ [b]) :
    ResidualAdj T cuts u v := by
  have huv : Pre u v := by subst v; exact List.prefix_append u [b]
  refine ⟨⟨valid_ancestor hv huv,hv,Or.inl ⟨b,he⟩⟩,?_⟩
  intro p hp
  constructor
  · rintro ⟨hup,hvp⟩
    have hpr := hr.2 p hp (by simpa [hvp] using (List.prefix_rfl : Pre v v))
    have hl := (hpr.trans hu).length_le
    have hvlen := congrArg List.length he
    rw [hvp] at hvlen
    simp only [List.length_append,List.length_singleton] at hvlen
    omega
  · rintro ⟨hvp,hup⟩
    have hvlen := congrArg List.length he
    have hplen := congrArg List.length hvp
    rw [hup] at hvlen
    simp only [List.length_append,List.length_singleton,List.length_dropLast] at *
    omega

/-- The original root-to-vertex path, retaining all suppressed vertices. -/
theorem region_walk {T cuts r v} (hv : Valid T v) (h : Region cuts r v) :
    ResidualWalk T cuts r v := by
  obtain ⟨q,hq⟩ := h.1
  subst v
  induction q generalizing r with
  | nil => simpa using (ResidualWalk.refl (cuts := cuts) hv)
  | cons b q ih =>
    have he : r ++ b :: q = (r ++ [b]) ++ q := by simp
    rw [he] at hv h
    have hp : Pre (r ++ [b]) ((r ++ [b]) ++ q) := List.prefix_append _ _
    have hpre : Pre r (r ++ [b]) := List.prefix_append _ _
    have hm := region_ancestor h hpre hp
    have ht : Region cuts (r ++ [b]) ((r ++ [b]) ++ q) :=
      ⟨hp,fun p hpm hpp => (h.2 p hpm hpp).trans hpre⟩
    simpa only [he] using ResidualWalk.step
      (region_down_edge hm List.prefix_rfl (valid_ancestor hv hp) b rfl) (ih hv ht)

theorem region_connected {T cuts r u v} (hu : Valid T u) (hv : Valid T v)
    (hru : Region cuts r u) (hrv : Region cuts r v) : ResidualWalk T cuts u v :=
  (region_walk hu hru).reverse.trans (region_walk hv hrv)

/-- Any two different rooted regions are separated by a recorded cut. -/
theorem rooted_regions_disjoint {cuts r s v}
    (hr : r = [] ∨ r ∈ cuts) (hs : s = [] ∨ s ∈ cuts)
    (hru : Region cuts r v) (hsv : Region cuts s v) : r = s := by
  have hrs : Pre r s := by
    rcases hr with he | hm
    · subst r; exact List.nil_prefix
    · exact hsv.2 r hm hru.1
  have hsr : Pre s r := by
    rcases hs with he | hm
    · subst s; exact List.nil_prefix
    · exact hru.2 s hm hsv.1
  exact hrs.eq_of_length_le hsr.length_le

/-- Exact characterization: a rooted region is one full residual component. -/
theorem region_component {T cuts r u v} (hr : r = [] ∨ r ∈ cuts)
    (hu : Valid T u) (hru : Region cuts r u) :
    ResidualWalk T cuts u v ↔ Valid T v ∧ Region cuts r v := by
  constructor
  · intro hw
    have hv := hw.finish
    have hrv : Pre r v := by
      rcases hr with he | hm
      · subst r; exact List.nil_prefix
      · exact (residual_walk_prefix_same hw hm).1 hru.1
    refine ⟨hv,hrv,?_⟩
    intro p hp hpv
    exact hru.2 p hp ((residual_walk_prefix_same hw hp).2 hpv)
  · rintro ⟨hv,hrv⟩
    exact region_connected hu hv hru hrv

end Universal233.CutRealization
