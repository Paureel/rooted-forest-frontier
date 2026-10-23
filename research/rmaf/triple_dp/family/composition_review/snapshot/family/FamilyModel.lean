import ConnectedRegions

/-! Finite labelled address trees and raw families. The convex hull is the
least path-convex set, defined logically rather than by an executable graph
algorithm. No correspondence with RMAF.minimalVertices is imported. -/
namespace TripleDP.Family

abbrev Support := Address → Prop

def names : BTree α → List α
  | .leaf x => [x]
  | .node l r => names l ++ names r

def vertices : BTree α → List Address
  | .leaf _ => [[]]
  | .node l r => [] :: ((vertices l).map (false :: ·) ++
                        (vertices r).map (true :: ·))

def vertex : BTree α → Address → Prop
  | .leaf _, [] => True
  | .leaf _, _ :: _ => False
  | .node _ _, [] => True
  | .node l _, false :: p => vertex l p
  | .node _ r, true :: p => vertex r p

def label : BTree α → Address → Option α
  | .leaf x, [] => some x
  | .leaf _, _ :: _ => none
  | .node _ _, [] => none
  | .node l _, false :: p => label l p
  | .node _ r, true :: p => label r p

def Leaf (t : BTree α) (v : Address) : Prop := ∃ x, label t v = some x

structure LabelledTree (α : Type) where
  tree : BTree α
  distinct : (names tree).Nodup

theorem vertex_iff_mem (t : BTree α) (v : Address) :
    vertex t v ↔ v ∈ vertices t := by
  induction t generalizing v with
  | leaf x => cases v <;> simp [vertex, vertices]
  | node l r hl hr =>
      cases v with
      | nil => simp [vertex, vertices]
      | cons side rest =>
          cases side <;> simp [vertex, vertices, List.mem_map, hl, hr]

theorem leaf_vertex (t : BTree α) (v : Address) (h : Leaf t v) : vertex t v := by
  induction t generalizing v with
  | leaf x => cases v <;> simp_all [Leaf, label, vertex]
  | node l r hl hr =>
      cases v with
      | nil => simp_all [Leaf, label]
      | cons side rest =>
          cases side
          · exact hl rest h
          · exact hr rest h

theorem root_vertex (t : BTree α) : vertex t [] := by cases t <;> trivial

theorem vertices_prefixClosed (t : BTree α) : PrefixClosed (vertex t) := by
  intro a ha p hp
  induction t generalizing a p with
  | leaf x =>
      cases a with
      | nil => have he := List.prefix_nil.mp hp; subst p; trivial
      | cons x xs => simp [vertex] at ha
  | node l r hl hr =>
      cases p with
      | nil => trivial
      | cons side rest =>
          cases a with
          | nil => simp at hp
          | cons other tail =>
              rcases List.cons_prefix_cons.mp hp with ⟨heq, hrest⟩
              subst other
              cases side
              · exact hl tail ha rest hrest
              · exact hr tail ha rest hrest

theorem vertices_pathConvex (t : BTree α) : PathConvex (vertex t) :=
  (rooted_pathConvex_iff_prefixClosed _ (root_vertex t)).mpr (vertices_prefixClosed t)

def Hull (seeds : Support) : Support :=
  fun v => ∀ R : Support, PathConvex R → (∀ x, seeds x → R x) → R v

theorem hull_contains {seeds : Support} {v : Address} (hv : seeds v) : Hull seeds v := by
  intro R hR hseeds
  exact hseeds v hv

theorem hull_least {seeds R : Support} (hR : PathConvex R)
    (hseeds : ∀ v, seeds v → R v) : ∀ v, Hull seeds v → R v := by
  intro v hv
  exact hv R hR hseeds

theorem hull_pathConvex (seeds : Support) : PathConvex (Hull seeds) := by
  intro a b ha hb v hv R hR hseeds
  exact hR a b (ha R hR hseeds) (hb R hR hseeds) v hv

theorem hull_idempotent (seeds : Support) : Hull (Hull seeds) = Hull seeds := by
  funext v
  apply propext
  exact ⟨hull_least (hull_pathConvex seeds) (fun _ h => h) v, hull_contains⟩

def LeafSet (t : BTree α) (R : Support) : Support := fun v => Leaf t v ∧ R v
def HasLeaf (t : BTree α) (R : Support) : Prop := ∃ v, LeafSet t R v
def ClosedHull (t : BTree α) (R : Support) := Hull (LeafSet t R)
def OpenHull (t : BTree α) (R : Support) := Hull (fun v => LeafSet t R v ∨ v = [])

theorem closedHull_subset (t : BTree α) (R : Support) (hR : PathConvex R) :
    ∀ v, ClosedHull t R v → R v := hull_least hR (fun _ h => h.2)

theorem openHull_subset (t : BTree α) (R : Support)
    (hR : PathConvex R) (root : R []) : ∀ v, OpenHull t R v → R v := by
  apply hull_least hR
  intro v hv
  rcases hv with hv | rfl
  · exact hv.2
  · exact root

theorem closedHull_labels (t : BTree α) (R : Support) (hR : PathConvex R) :
    LeafSet t (ClosedHull t R) = LeafSet t R := by
  funext v
  apply propext
  constructor
  · intro h
    exact ⟨h.1, closedHull_subset t R hR v h.2⟩
  · intro h
    exact ⟨h.1, hull_contains h⟩

theorem openHull_labels (t : BTree α) (R : Support)
    (hR : PathConvex R) (root : R []) : LeafSet t (OpenHull t R) = LeafSet t R := by
  funext v
  apply propext
  constructor
  · intro h
    exact ⟨h.1, openHull_subset t R hR root v h.2⟩
  · intro h
    exact ⟨h.1, hull_contains (Or.inl h)⟩

/-- Raw open supports may be leafless; they are uncharged and will be pruned.
Closed supports are charged and therefore must contain a leaf. -/
structure RawFamily (t : BTree α) (k : Nat) where
  closed : Fin k → Support
  openRegion : Option Support
  closed_convex : ∀ i, PathConvex (closed i)
  closed_inside : ∀ i v, closed i v → vertex t v
  closed_live : ∀ i, HasLeaf t (closed i)
  closed_root : ∀ i, ¬ closed i []
  closed_disjoint : ∀ i j v, closed i v → closed j v → i = j
  open_convex : ∀ R, openRegion = some R → PathConvex R
  open_inside : ∀ R, openRegion = some R → ∀ v, R v → vertex t v
  open_root : ∀ R, openRegion = some R → R []
  open_disjoint : ∀ R, openRegion = some R → ∀ i v, R v → closed i v → False
  covers : ∀ v, Leaf t v → (∃ i, closed i v) ∨ ∃ R, openRegion = some R ∧ R v

def Retained (F : RawFamily t k) : Prop :=
  ∀ R, F.openRegion = some R → HasLeaf t R

def closedCost (_ : RawFamily t k) : Nat := k

#print axioms vertex_iff_mem
#print axioms leaf_vertex
#print axioms vertices_pathConvex
#print axioms hull_contains
#print axioms hull_least
#print axioms hull_pathConvex
#print axioms hull_idempotent
#print axioms closedHull_subset
#print axioms openHull_subset
#print axioms closedHull_labels
#print axioms openHull_labels
end TripleDP.Family
