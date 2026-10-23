import RMAF

/-! Problem-specific source-graph proof module. No optimum oracle is used.
The graph is the actual unsuppressed parent/child graph of RMAF.Tree.
The local cherry results do not assume any cherry coverage property. -/
namespace Universal233.CoreGraph
open RMAF

/-- Actual subtree lookup. Addresses run from the root toward a vertex. -/
def subtree : Tree → Vertex → Option Tree
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .node l r, b :: v => subtree (if b then r else l) v

def Valid (t : Tree) (v : Vertex) : Prop := ∃ s, subtree t v = some s

def LeafAt (t : Tree) (v : Vertex) (x : Nat) : Prop :=
  subtree t v = some (.leaf x)

def CherryAt (t : Tree) (p : Vertex) (x y : Nat) : Prop :=
  subtree t p = some (.node (.leaf x) (.leaf y))

def Adj (t : Tree) (u v : Vertex) : Prop :=
  Valid t u ∧ Valid t v ∧
  ((∃ b : Bool, v = u ++ [b]) ∨ (∃ b : Bool, u = v ++ [b]))

/-- Finite walks in an explicitly supplied subset of the actual source graph. -/
inductive Walk (t : Tree) (P : Vertex → Prop) : Vertex → Vertex → Prop
  | refl {x} : P x → Walk t P x x
  | step {x y z} : P x → Adj t x y → Walk t P y z → Walk t P x z

theorem Walk.start {t P x y} (w : Walk t P x y) : P x := by
  cases w with
  | refl h => exact h
  | step h _ _ => exact h

theorem Walk.finish {t P x y} (w : Walk t P x y) : P y := by
  induction w with
  | refl h => exact h
  | step _ _ _ ih => exact ih

theorem Adj.symm {t u v} (h : Adj t u v) : Adj t v u :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem Adj.ne {t u v} (h : Adj t u v) : u ≠ v := by
  intro he
  rcases h.2.2 with ⟨b, hb⟩ | ⟨b, hb⟩
  · have hl := congrArg List.length hb
    simp only [List.length_append, List.length_singleton] at hl
    rw [he] at hl
    omega
  · have hl := congrArg List.length hb
    simp only [List.length_append, List.length_singleton] at hl
    rw [he] at hl
    omega

theorem Walk.trans {t P x y z} (w : Walk t P x y) (v : Walk t P y z) :
    Walk t P x z := by
  induction w with
  | refl _ => exact v
  | step h a _ ih => exact .step h a (ih v)

theorem Walk.mono {t P Q x y} (w : Walk t P x y) (h : ∀ v, P v → Q v) :
    Walk t Q x y := by
  induction w with
  | refl hp => exact .refl (h _ hp)
  | step hp a _ ih => exact .step (h _ hp) a ih

theorem Walk.reverse {t P x y} (w : Walk t P x y) : Walk t P y x := by
  induction w with
  | refl hp => exact .refl hp
  | step hp a tail ih =>
      exact ih.trans (.step tail.start a.symm (.refl hp))

/-- Removing a vertex having at most one neighbor in a support preserves
connectedness between all remaining vertices. The proof removes excursions
through that vertex from actual walks. -/
theorem Walk.avoid_one_neighbor {t P bad x y} (w : Walk t P x y)
    (hy : y ≠ bad)
    (unique : ∀ u v, Adj t bad u → P u → Adj t bad v → P v → u = v) :
    (x ≠ bad → Walk t (fun z => P z ∧ z ≠ bad) x y) ∧
    (x = bad → ∀ u, Adj t bad u → P u →
      Walk t (fun z => P z ∧ z ≠ bad) u y) := by
  induction w with
  | refl hp =>
      constructor
      · intro hx
        exact .refl ⟨hp, hx⟩
      · intro hx
        exact False.elim (hy hx)
  | @step x z y hp a tail ih =>
      constructor
      · intro hx
        by_cases hz : z = bad
        · exact (ih hy).2 hz x (hz ▸ a.symm) hp
        · exact .step ⟨hp, hx⟩ a ((ih hy).1 hz)
      · intro hx u au hu
        subst x
        have hz : z ≠ bad := fun he => a.ne he.symm
        have he : u = z := unique u z au hu a tail.start
        simpa [he] using (ih hy).1 hz

theorem subtree_append {t s : Tree} {p : Vertex}
    (h : subtree t p = some s) (v : Vertex) :
    subtree t (p ++ v) = subtree s v := by
  induction p generalizing t with
  | nil => simp [subtree] at h; subst s; rfl
  | cons b p ih =>
      cases t with
      | leaf x => simp [subtree] at h
      | node l r =>
          simpa [subtree] using ih h

theorem cherry_left {t p x y} (h : CherryAt t p x y) :
    LeafAt t (p ++ [false]) x := by
  simpa [LeafAt, subtree] using subtree_append h [false]

theorem cherry_right {t p x y} (h : CherryAt t p x y) :
    LeafAt t (p ++ [true]) y := by
  simpa [LeafAt, subtree] using subtree_append h [true]

theorem cherry_parent_valid {t p x y} (h : CherryAt t p x y) : Valid t p :=
  ⟨_, h⟩

theorem cherry_parent_not_terminal {t p x y v z} (h : CherryAt t p x y)
    (hv : LeafAt t v z) : v ≠ p := by
  intro he
  subst v
  unfold LeafAt at hv
  rw [h] at hv
  cases hv

/-- The only neighbors below a cherry parent are its two actual leaf children.
Every other neighbor is the unique address obtained by deleting the final bit.
The latter case is impossible when the cherry parent is the original root. -/
theorem cherry_neighbor_cases {t p x y v} (h : CherryAt t p x y)
    (a : Adj t p v) :
    v = p ++ [false] ∨ v = p ++ [true] ∨ v = p.dropLast := by
  rcases a.2.2 with ⟨b, hb⟩ | ⟨b, hb⟩
  · cases b
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
  · right; right
    have hd := congrArg List.dropLast hb
    simpa using hd.symm

theorem cherry_adj_left {t p x y} (h : CherryAt t p x y) :
    Adj t p (p ++ [false]) :=
  ⟨cherry_parent_valid h, ⟨_, cherry_left h⟩, Or.inl ⟨false, rfl⟩⟩

theorem cherry_adj_right {t p x y} (h : CherryAt t p x y) :
    Adj t p (p ++ [true]) :=
  ⟨cherry_parent_valid h, ⟨_, cherry_right h⟩, Or.inl ⟨true, rfl⟩⟩

theorem LeafAt.valid {t v x} (h : LeafAt t v x) : Valid t v := ⟨_, h⟩

/-- A genuine leaf has no child edge, including at the original root. -/
theorem leaf_no_child {t v x} (h : LeafAt t v x) (b : Bool) :
    ¬ Valid t (v ++ [b]) := by
  rintro ⟨s, hs⟩
  have he := subtree_append h [b]
  simp [subtree] at he
  rw [he] at hs
  contradiction

/-- Every neighbor of a nonroot actual leaf is its actual parent. -/
theorem leaf_neighbor_parent {t p b x v}
    (h : LeafAt t (p ++ [b]) x) (a : Adj t (p ++ [b]) v) : v = p := by
  rcases a.2.2 with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact False.elim (leaf_no_child h c (hc ▸ a.2.1))
  · have hd := congrArg List.dropLast hc
    simpa using hd.symm

/-- Every nontrivial walk from a cherry leaf visits its parent. This uses only
actual one-edge graph adjacency; no convexity or span-intersection axiom. -/
theorem walk_from_leaf_visits_parent {t P p b x z}
    (h : LeafAt t (p ++ [b]) x) (w : Walk t P (p ++ [b]) z)
    (hne : z ≠ p ++ [b]) : P p := by
  cases w with
  | refl _ => exact False.elim (hne rfl)
  | @step u v z hu hadj tail =>
      have hv : v = p := leaf_neighbor_parent h hadj
      simpa [hv] using tail.start

/-- A partition of actual source leaves with vertex-disjoint connected source
supports. Supports may retain degree-two vertices and the original root.
All structural fields are the ordinary graph/partition conditions; there is
no field stating any generator coverage, contraction, cut lift or bound. -/
structure SourcePartition (t : Tree) where
  owner : Vertex → Nat
  support : Nat → Vertex → Prop
  actual : ∀ i v, support i v → Valid t v
  terminal_exact : ∀ i v x, LeafAt t v x → (support i v ↔ owner v = i)
  connected : ∀ i u v, support i u → support i v → Walk t (support i) u v
  disjoint : ∀ i j v, support i v → support j v → i = j

/-- A current leaf is the only source leaf in its partition block. -/
def SingletonBlock {t} (P : SourcePartition t) (u : Vertex) : Prop :=
  ∀ v x, LeafAt t v x → P.owner v = P.owner u → v = u

def Monochromatic {t} (P : SourcePartition t) (color : Nat → Nat) : Prop :=
  ∀ u v x y, LeafAt t u x → LeafAt t v y →
    P.owner u = P.owner v → color x = color y

theorem own_terminal {t} (P : SourcePartition t) {u x} (h : LeafAt t u x) :
    P.support (P.owner u) u := (P.terminal_exact _ _ _ h).mpr rfl

/-- If a leaf block has another terminal, its connected support contains the
actual parent. -/
theorem nonsingleton_parent {t p b x} (P : SourcePartition t)
    (h : LeafAt t (p ++ [b]) x) (hn : ¬ SingletonBlock P (p ++ [b])) :
    P.support (P.owner (p ++ [b])) p := by
  classical
  have hex : ∃ v z, LeafAt t v z ∧ P.owner v = P.owner (p ++ [b]) ∧
      v ≠ p ++ [b] := by
    apply Classical.byContradiction
    intro he
    apply hn
    intro v z hv ho
    apply Classical.byContradiction
    intro hne
    exact he ⟨v, z, hv, ho, hne⟩
  obtain ⟨v, z, hv, ho, hne⟩ := hex
  have hs := (P.terminal_exact _ _ _ hv).mpr ho
  exact walk_from_leaf_visits_parent h
    (P.connected _ _ _ (own_terminal P h) hs) hne

/-- Universal mixed-cherry singleton alternative in the actual source graph.
This is a local coverage prerequisite, not the full recursive coverage theorem. -/
theorem mixed_cherry_singleton {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) (color : Nat → Nat)
    (hm : Monochromatic P color) (hc : color x ≠ color y) :
    SingletonBlock P (p ++ [false]) ∨ SingletonBlock P (p ++ [true]) := by
  classical
  by_cases hl : SingletonBlock P (p ++ [false])
  · exact Or.inl hl
  · by_cases hr : SingletonBlock P (p ++ [true])
    · exact Or.inr hr
    · have hpl := nonsingleton_parent P (cherry_left h) hl
      have hpr := nonsingleton_parent P (cherry_right h) hr
      have hid := P.disjoint _ _ _ hpl hpr
      exact False.elim (hc (hm _ _ _ _ (cherry_left h) (cherry_right h) hid))

/-- A color occurring at exactly one current source leaf forces that leaf's
partition block to be a singleton. No optimizer is queried. -/
theorem unique_color_singleton {t u x} (P : SourcePartition t)
    (h : LeafAt t u x) (color : Nat → Nat) (hm : Monochromatic P color)
    (unique : ∀ v y, LeafAt t v y → color y = color x → v = u) :
    SingletonBlock P u := by
  intro v y hv ho
  exact unique v y hv (hm _ _ _ _ hv h ho)

/-- The local alternative remains valid at a cherry whose parent is the
original root; the root itself is never treated as a cuttable edge. -/
theorem mixed_root_cherry_singleton {x y} (P : SourcePartition (.node (.leaf x) (.leaf y)))
    (color : Nat → Nat) (hm : Monochromatic P color) (hc : color x ≠ color y) :
    SingletonBlock P [false] ∨ SingletonBlock P [true] := by
  exact mixed_cherry_singleton P (p := []) rfl color hm hc

#print axioms subtree_append
#print axioms leaf_no_child
#print axioms leaf_neighbor_parent
#print axioms walk_from_leaf_visits_parent
#print axioms nonsingleton_parent
#print axioms mixed_cherry_singleton
#print axioms unique_color_singleton
#print axioms mixed_root_cherry_singleton
end Universal233.CoreGraph
