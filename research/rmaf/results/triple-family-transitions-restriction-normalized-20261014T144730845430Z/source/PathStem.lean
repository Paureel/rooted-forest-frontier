import ConnectedRegions

/-! One-shot problem-specific path route. No new family assembly or DP
correspondence is assumed. Addresses use false/true for the two child edges. -/
namespace TripleDP.PathRoute

/-- Finite vertices, including internal vertices, of an actual labelled tree. -/
def vertices {α : Type} : BTree α → List Address
  | .leaf _ => [[]]
  | .node l r => [] :: ((vertices l).map (false :: ·) ++ (vertices r).map (true :: ·))

/-- Labels remain attached to their actual leaf addresses. -/
def leafEntries {α : Type} : BTree α → List (Address × α)
  | .leaf x => [([], x)]
  | .node l r =>
      (leafEntries l).map (fun p => (false :: p.1, p.2)) ++
      (leafEntries r).map (fun p => (true :: p.1, p.2))

def IsLeaf {α : Type} (t : BTree α) (a : Address) : Prop :=
  ∃ x, (a, x) ∈ leafEntries t

/-- A pinned finite labelled-tree model with unique leaf labels. -/
structure LabelledTree (α : Type) where
  tree : BTree α
  uniqueLabels : ((leafEntries tree).map Prod.snd).Nodup

/-- Union of the unique root-to-label paths. -/
def RootHull (labels : Address → Prop) (v : Address) : Prop :=
  ∃ a, labels a ∧ v <+: a

/-- Root-path trim of the labels actually present in the input support. -/
def openTrim (leaf region : Address → Prop) : Address → Prop :=
  RootHull (fun a => leaf a ∧ region a)

theorem rootHull_unique_paths (labels : Address → Prop) (v : Address) :
    RootHull labels v ↔ ∃ a, labels a ∧ OnPath [] a v := by
  constructor
  · rintro ⟨a, ha, hva⟩
    exact ⟨a, ha, by simp [OnPath, lca, hva]⟩
  · rintro ⟨a, ha, _, hv⟩
    refine ⟨a, ha, ?_⟩
    rcases hv with hv | hv
    · have hnil := List.prefix_nil.mp hv
      subst v
      simp
    · exact hv

theorem rootHull_root_iff (labels : Address → Prop) :
    RootHull labels [] ↔ ∃ a, labels a := by
  simp [RootHull]

theorem rootHull_contains_label (labels : Address → Prop) (a : Address)
    (ha : labels a) : RootHull labels a :=
  ⟨a, ha, List.prefix_rfl⟩

theorem rootHull_prefixClosed (labels : Address → Prop) :
    PrefixClosed (RootHull labels) := by
  rintro a ⟨b, hb, hab⟩ p hpa
  exact ⟨b, hb, hpa.trans hab⟩

theorem rootHull_pathConvex (labels : Address → Prop) :
    PathConvex (RootHull labels) := by
  intro a b ha hb v hv
  rcases hv.2 with hva | hvb
  · exact rootHull_prefixClosed labels a ha v hva
  · exact rootHull_prefixClosed labels b hb v hvb

/-- This universal property fixes the rooted hull geometrically: it is the
least path-convex support containing the root and all labels, if labels exist. -/
theorem rootHull_minimal (labels region : Address → Prop)
    (convex : PathConvex region) (root : region [])
    (contains : ∀ a, labels a → region a) :
    ∀ v, RootHull labels v → region v := by
  rintro v ⟨a, ha, hva⟩
  exact (rooted_pathConvex_iff_prefixClosed region root).mp convex
    a (contains a ha) v hva

theorem openTrim_subset (leaf region : Address → Prop)
    (convex : PathConvex region) (root : region []) :
    ∀ v, openTrim leaf region v → region v :=
  rootHull_minimal _ region convex root (fun _ h => h.2)

theorem openTrim_preserves_labels (leaf region : Address → Prop)
    (convex : PathConvex region) (root : region []) (a : Address)
    (isLeaf : leaf a) : openTrim leaf region a ↔ region a := by
  constructor
  · exact openTrim_subset leaf region convex root a
  · intro ha
    exact rootHull_contains_label _ a ⟨isLeaf, ha⟩

theorem openTrim_root_iff (leaf region : Address → Prop) :
    openTrim leaf region [] ↔ ∃ a, leaf a ∧ region a :=
  rootHull_root_iff _

/-- Every retained vertex witnesses a descendant label. This applies at any
subtree root, not only at the two children of the ambient root. -/
theorem rootHull_subtree_occupied_iff (labels : Address → Prop) (p : Address) :
    (∃ v, p <+: v ∧ RootHull labels v) ↔ ∃ a, labels a ∧ p <+: a := by
  constructor
  · rintro ⟨v, hpv, a, ha, hva⟩
    exact ⟨a, ha, hpv.trans hva⟩
  · rintro ⟨a, ha, hpa⟩
    exact ⟨a, hpa, rootHull_contains_label labels a ha⟩

/-- Exact leafless-child exclusion; raw rooted convex supports do not satisfy it. -/
theorem openTrim_child_occupied_iff (leaf region : Address → Prop) (side : Bool) :
    (∃ v, openTrim leaf region (side :: v)) ↔
      ∃ a, leaf (side :: a) ∧ region (side :: a) := by
  constructor
  · rintro ⟨v, a, ha, hva⟩
    cases a with
    | nil => simp at hva
    | cons other tail =>
        have heq := (List.cons_prefix_cons.mp hva).1
        subst other
        exact ⟨tail, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, rootHull_contains_label _ _ ha⟩

theorem openTrim_no_leafless_child (leaf region : Address → Prop) (side : Bool)
    (noLabel : ¬ ∃ a, leaf (side :: a) ∧ region (side :: a)) :
    ∀ v, ¬ openTrim leaf region (side :: v) := by
  intro v hv
  exact noLabel ((openTrim_child_occupied_iff leaf region side).mp ⟨v, hv⟩)

/-- Root-path trimming commutes exactly with restricting both the leaf predicate
and the support to a child, including the empty-child case. -/
theorem openTrim_child_restriction (leaf region : Address → Prop)
    (side : Bool) (v : Address) :
    openTrim leaf region (side :: v) ↔
      openTrim (fun a => leaf (side :: a)) (fun a => region (side :: a)) v := by
  constructor
  · rintro ⟨a, ha, hva⟩
    cases a with
    | nil => simp at hva
    | cons other tail =>
        rcases List.cons_prefix_cons.mp hva with ⟨heq, htail⟩
        subst other
        exact ⟨tail, ha, htail⟩
  · rintro ⟨a, ha, hva⟩
    exact ⟨side :: a, ha, List.cons_prefix_cons.mpr ⟨rfl, hva⟩⟩

/-- The leafless open fragment is empty after trimming, hence can be discarded.
No theorem here promotes an empty fragment into a charged region. -/
theorem openTrim_empty_if_leafless (leaf region : Address → Prop)
    (noLabel : ¬ ∃ a, leaf a ∧ region a) :
    ∀ v, ¬ openTrim leaf region v := by
  rintro v ⟨a, ha, _⟩
  exact noLabel ⟨a, ha⟩

/-- Arbitrary pointwise shrinking preserves the actual support disjointness,
without merging adjacent or same-colour region indices. -/
theorem shrinking_preserves_disjointness {ι : Type}
    (before after : ι → Address → Prop)
    (disjoint : ∀ i j v, before i v → before j v → i = j)
    (shrink : ∀ i v, after i v → before i v) :
    ∀ i j v, after i v → after j v → i = j := by
  intro i j v hi hj
  exact disjoint i j v (shrink i v hi) (shrink j v hj)

/-- Actual finite-tree specialization. The support stays on the given tree,
its leaf labels are unchanged, and every retained child contains such a label. -/
theorem finite_tree_open_trim {α : Type} (t : LabelledTree α)
    (region : Address → Prop)
    (valid : ∀ v, region v → v ∈ vertices t.tree)
    (convex : PathConvex region) (root : region [])
    (nonemptyLabels : ∃ a, IsLeaf t.tree a ∧ region a) :
    PathConvex (openTrim (IsLeaf t.tree) region) ∧
    openTrim (IsLeaf t.tree) region [] ∧
    (∀ v, openTrim (IsLeaf t.tree) region v → region v) ∧
    (∀ v, openTrim (IsLeaf t.tree) region v → v ∈ vertices t.tree) ∧
    (∀ a, IsLeaf t.tree a → (openTrim (IsLeaf t.tree) region a ↔ region a)) ∧
    (∀ side, (∃ v, openTrim (IsLeaf t.tree) region (side :: v)) ↔
      ∃ a, IsLeaf t.tree (side :: a) ∧ region (side :: a)) := by
  refine ⟨rootHull_pathConvex _, (openTrim_root_iff _ _).mpr nonemptyLabels,
    openTrim_subset _ _ convex root, ?_, ?_, openTrim_child_occupied_iff _ _⟩
  · intro v hv
    exact valid v (openTrim_subset _ _ convex root v hv)
  · intro a ha
    exact openTrim_preserves_labels _ _ convex root a ha

#print axioms rootHull_unique_paths
#print axioms rootHull_root_iff
#print axioms rootHull_contains_label
#print axioms rootHull_prefixClosed
#print axioms rootHull_pathConvex
#print axioms rootHull_minimal
#print axioms openTrim_subset
#print axioms openTrim_preserves_labels
#print axioms openTrim_root_iff
#print axioms rootHull_subtree_occupied_iff
#print axioms openTrim_child_occupied_iff
#print axioms openTrim_no_leafless_child
#print axioms openTrim_child_restriction
#print axioms openTrim_empty_if_leafless
#print axioms shrinking_preserves_disjointness
#print axioms finite_tree_open_trim
end TripleDP.PathRoute
