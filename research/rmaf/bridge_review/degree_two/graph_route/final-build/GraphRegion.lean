import PureBridge

/-! Graph-level realization of rooted regions. Adjacency is the actual parent/
child adjacency of binary addresses. Connectedness is given by finite walks,
not by prefix convexity or the conclusion of the consumer theorem. -/
namespace BridgeReview
open PureBridge

def Adj (u v : Address) : Prop :=
  (∃ b : Bool, v = u ++ [b]) ∨ (∃ b : Bool, u = v ++ [b])

inductive Walk (P : Address → Prop) : Address → Address → Prop
  | refl {x} : P x → Walk P x x
  | step {x y z} : Walk P x y → Adj y z → P z → Walk P x z

theorem Walk.start {P : Address → Prop} {x y : Address} (w : Walk P x y) : P x := by
  induction w with
  | refl h => exact h
  | step _ _ _ ih => exact ih

theorem Walk.finish {P : Address → Prop} {x y : Address} (w : Walk P x y) : P y := by
  cases w with
  | refl h => exact h
  | step _ _ h => exact h

/-- A minimum-depth vertex of a graph-connected set is an ancestor of every
vertex. An upward edge cannot leave that ancestor's descendants, because its
endpoint would be shorter than the minimum. -/
theorem walk_below_minimum {P : Address → Prop} {r y : Address}
    (w : Walk P r y) (hmin : ∀ z, P z → r.length ≤ z.length) : r.IsPrefix y := by
  induction w with
  | refl _ => exact List.prefix_refl _
  | @step u v w hadj hv ih =>
    rcases hadj with ⟨b, rfl⟩ | ⟨b, hu⟩
    · exact ih.trans (List.prefix_append _ _)
    · have hvu : v.IsPrefix u := ⟨[b], hu.symm⟩
      exact List.prefix_of_prefix_length_le ih hvu (hmin v hv)

/-- Every ancestor between the starting point and the endpoint is visited by
any graph walk. This is proved from one-edge adjacency, not assumed convexity. -/
theorem walk_ancestor_between {P : Address → Prop} {r y : Address}
    (w : Walk P r y) (x : Address) (hrx : r.IsPrefix x) (hxy : x.IsPrefix y) : P x := by
  induction w with
  | refl hr =>
    have h : x = r := hxy.eq_of_length_le hrx.length_le
    simpa [h] using hr
  | @step u v w hadj hv ih =>
    rcases hadj with ⟨b, hdown⟩ | ⟨b, hup⟩
    · have huv : u.IsPrefix v := ⟨[b], hdown.symm⟩
      by_cases hxu : x.length ≤ u.length
      · exact ih (List.prefix_of_prefix_length_le hxy huv hxu)
      · have hlen : x.length = v.length := by
          have hxv := hxy.length_le
          have hstep : v.length = u.length + 1 := by simp [hdown]
          omega
        have heq := hxy.eq_of_length hlen
        simpa [heq] using hv
    · have hvu : v.IsPrefix u := ⟨[b], hup.symm⟩
      exact ih (hxy.trans hvu)

/-- This minimum is obtained from a finite list, not supplied as a geometric
assumption. Duplicate vertices in the list are harmless. -/
theorem exists_shortest (a : Address) (xs : List Address) :
    ∃ r, r ∈ a :: xs ∧ ∀ v, v ∈ a :: xs → r.length ≤ v.length := by
  induction xs generalizing a with
  | nil =>
    refine ⟨a, by simp, ?_⟩
    intro v hv
    have h : v = a := by simpa using hv
    simp [h]
  | cons b xs ih =>
    obtain ⟨r, hr, hmin⟩ := ih b
    by_cases har : a.length ≤ r.length
    · refine ⟨a, by simp, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · simp [h]
      · exact Nat.le_trans har (hmin v h)
    · refine ⟨r, by simp [hr], ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · subst v; omega
      · exact hmin v h

/-- Finite nonempty graph-connected support. The relation used here is ordinary
parent/child graph adjacency; there are no rooted-convexity fields. -/
structure ConnectedSupport where
  first : Address
  rest : List Address
  connected : ∀ u, u ∈ first :: rest → ∀ v, v ∈ first :: rest →
    Walk (fun x => x ∈ first :: rest) u v

namespace ConnectedSupport
noncomputable def root (s : ConnectedSupport) : Address :=
  Classical.choose (exists_shortest s.first s.rest)

theorem root_mem (s : ConnectedSupport) : s.root ∈ s.first :: s.rest :=
  (Classical.choose_spec (exists_shortest s.first s.rest)).1

theorem root_shortest (s : ConnectedSupport) :
    ∀ v, v ∈ s.first :: s.rest → s.root.length ≤ v.length :=
  (Classical.choose_spec (exists_shortest s.first s.rest)).2

/-- The missing graph-to-region construction: the full vertex support is
retained, including degree-two vertices and a possible ambient root. -/
noncomputable def toRootedRegion (s : ConnectedSupport) : RootedRegion where
  root := s.root
  member := fun v => v ∈ s.first :: s.rest
  root_mem := s.root_mem
  below := fun v hv => walk_below_minimum (s.connected _ s.root_mem v hv) s.root_shortest
  convex := fun x y hrx hxy hy =>
    walk_ancestor_between (s.connected _ s.root_mem y hy) x hrx hxy

/-- The minimum-depth root is unique, so this construction agrees with any
other correctly computed minimum-depth vertex of the same graph support. -/
theorem root_unique (s : ConnectedSupport) (v : Address)
    (hv : v ∈ s.first :: s.rest)
    (hmin : ∀ z, z ∈ s.first :: s.rest → v.length ≤ z.length) : v = s.root := by
  have hprefix := s.toRootedRegion.below v hv
  exact (hprefix.eq_of_length_le (hmin s.root s.root_mem)).symm

/-- Exact original consumer instantiated at graph-connected supports. -/
theorem deepest_graph_root_in_neighbor (a b : ConnectedSupport)
    (hdepth : b.root.length ≤ a.root.length)
    (hoverlap : ∃ z, z ∈ a.first :: a.rest ∧ z ∈ b.first :: b.rest) :
    a.root ∈ b.first :: b.rest := by
  exact PureBridge.deepest_root_in_neighbor a.toRootedRegion b.toRootedRegion hdepth hoverlap

/-- Every neighboring graph support contains the chosen root, without a
neighborhood-size bound. -/
theorem deepest_graph_neighbors_intersect (a b c : ConnectedSupport)
    (hbdepth : b.root.length ≤ a.root.length)
    (hcdepth : c.root.length ≤ a.root.length)
    (hab : ∃ z, z ∈ a.first :: a.rest ∧ z ∈ b.first :: b.rest)
    (hac : ∃ z, z ∈ a.first :: a.rest ∧ z ∈ c.first :: c.rest) :
    ∃ z, z ∈ b.first :: b.rest ∧ z ∈ c.first :: c.rest := by
  exact ⟨a.root, deepest_graph_root_in_neighbor a b hbdepth hab,
    deepest_graph_root_in_neighbor a c hcdepth hac⟩
end ConnectedSupport

/-- A least connected support containing a nonempty list of terminal addresses
inside a finite ambient address list. This wrapper imposes no unique-label,
terminal-leaf, or ambient-tree invariant. Minimality means least support, not
rooted convexity. The region theorem below needs only connectedness. -/
structure MinimalEmbedding where
  ambient : List Address
  terminals : List Address
  terminal_nonempty : terminals ≠ []
  support : ConnectedSupport
  inAmbient : ∀ v, v ∈ support.first :: support.rest → v ∈ ambient
  containsTerminals : ∀ v, v ∈ terminals → v ∈ support.first :: support.rest
  minimal : ∀ other : ConnectedSupport,
    (∀ v, v ∈ other.first :: other.rest → v ∈ ambient) →
    (∀ v, v ∈ terminals → v ∈ other.first :: other.rest) →
    ∀ v, v ∈ support.first :: support.rest → v ∈ other.first :: other.rest

/-- G1: the actual finite graph support is carried unchanged into the existing
region interface. No edge is suppressed or vertex dropped by this map. -/
noncomputable def MinimalEmbedding.region (e : MinimalEmbedding) : RootedRegion :=
  e.support.toRootedRegion

theorem MinimalEmbedding.region_exact (e : MinimalEmbedding) (v : Address) :
    e.region.member v ↔ v ∈ e.support.first :: e.support.rest := Iff.rfl

theorem MinimalEmbedding.deepest_root_in_neighbor (a b : MinimalEmbedding)
    (hdepth : b.support.root.length ≤ a.support.root.length)
    (hoverlap : ∃ z, z ∈ a.support.first :: a.support.rest ∧
      z ∈ b.support.first :: b.support.rest) :
    a.support.root ∈ b.support.first :: b.support.rest :=
  ConnectedSupport.deepest_graph_root_in_neighbor a.support b.support hdepth hoverlap

#print axioms MinimalEmbedding.region
#print axioms MinimalEmbedding.region_exact
#print axioms MinimalEmbedding.deepest_root_in_neighbor

#print axioms Walk.start
#print axioms Walk.finish
#print axioms walk_below_minimum
#print axioms walk_ancestor_between
#print axioms exists_shortest
#print axioms ConnectedSupport.root_mem
#print axioms ConnectedSupport.root_shortest
#print axioms ConnectedSupport.root_unique
#print axioms ConnectedSupport.toRootedRegion
#print axioms ConnectedSupport.deepest_graph_root_in_neighbor
#print axioms ConnectedSupport.deepest_graph_neighbors_intersect
end BridgeReview
