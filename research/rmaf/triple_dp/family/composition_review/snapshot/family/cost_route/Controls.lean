import FamilyAssembly

namespace TripleDP.CostRoute
open TripleDP

variable {α : Type}

def singletonFamily (x : α) : Family (.leaf x) Unit where
  finite := ⟨[()], by simp, fun i => by cases i; simp⟩
  support := fun _ a => a = []
  bounded := by intro i a h; exact h
  convex := by
    intro i a b ha hb v hv
    subst a
    subst b
    exact List.prefix_nil.mp (hv.2.elim id id)
  labelled := fun _ => ⟨[], x, ⟨rfl, rfl⟩, rfl⟩
  disjoint := by intro i j a hi hj; cases i; cases j; rfl
  covers := by intro a y h; exact ⟨(), h.1⟩
  boundary := some ()
  root_spec := by intro i; cases i; simp

abbrev leftSingle : Family (.leaf 0) Unit := singletonFamily 0
abbrev rightSingle : Family (.leaf 1) Unit := singletonFamily 1
abbrev cherryClosed := closeBoth leftSingle rightSingle
abbrev cherryLeft := extendLeft leftSingle rightSingle () rfl
abbrev cherryRight := extendRight leftSingle rightSingle () rfl

/-- T1: exact cardinality and cost, plus unused internal root. -/
theorem t1_closed_count_cost :
    cherryClosed.blockCount = 2 ∧ cherryClosed.cost = 2 ∧
    (∀ i, ¬ cherryClosed.support i []) := by
  refine ⟨rfl, rfl, ?_⟩
  intro i
  cases i <;> simp [closeBoth, closedSupport, liftSupport]

theorem t1_leaf_owners :
    cherryClosed.support (.inl ()) [false] ∧
    cherryClosed.support (.inr ()) [true] ∧
    (Sum.inl () : Sum Unit Unit) ≠ .inr () := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, (by intro h; cases h)⟩

/-- T3: one-sided extension keeps two blocks and charges only the closed child. -/
theorem t3_extensions :
    cherryLeft.blockCount = 2 ∧ cherryLeft.cost = 1 ∧
    cherryRight.blockCount = 2 ∧ cherryRight.cost = 1 ∧
    cherryLeft.support (.inl ()) [] ∧ cherryRight.support (.inr ()) [] := by
  exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- T4: even identical color metadata do not identify the two adjacent regions.
The supports {root,left} and {right} share an edge and remain disjoint. -/
def adjacentSameColor := extendLeft (singletonFamily ((0, 7) : Nat × Nat)) (singletonFamily (1, 7)) () rfl

theorem t4_distinct_labels_same_color :
    ((0, 7) : Nat × Nat) ≠ (1, 7) ∧ (0, 7).2 = (1, 7).2 := by decide

theorem t4_adjacent_same_color_separate :
    adjacentSameColor.blockCount = 2 ∧
    adjacentSameColor.support (.inl ()) [] ∧
    adjacentSameColor.support (.inl ()) [false] ∧
    adjacentSameColor.support (.inr ()) [true] ∧
    (Sum.inl () : Sum Unit Unit) ≠ .inr () := by
  exact ⟨rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩,
    Or.inr ⟨rfl, rfl⟩, (by intro h; cases h)⟩

/-- T5: labelled singleton is open and receives exactly one closing charge. -/
theorem t5_singleton : leftSingle.blockCount = 1 ∧ leftSingle.cost = 0 ∧
    leftSingle.cost + boundaryCharge leftSingle.boundary = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Existing gapped support is regression evidence, not a fresh holdout. -/
theorem regression_gap : ¬ PathConvex gappedRegion := gapped_region_not_pathConvex

/-- Frozen incursion pair: same sole relevant leaf at [false], but one
support visits an extra leafless child vertex. The vertex model below is
only the address predicate regression, not a new charged family. -/
def withoutIncursion (a : Address) : Prop := a = [] ∨ a = [false]
def withIncursion (a : Address) : Prop := a = [] ∨ a = [false] ∨ a = [true]

theorem withIncursion_convex : PathConvex withIncursion := by
  apply (rooted_pathConvex_iff_prefixClosed withIncursion (Or.inl rfl)).mpr
  intro a ha p hp
  rcases ha with rfl | rfl | rfl
  · exact Or.inl (List.prefix_nil.mp hp)
  · cases p with
    | nil => exact Or.inl rfl
    | cons b bs =>
      rcases List.cons_prefix_cons.mp hp with ⟨rfl, hbs⟩
      have he := List.prefix_nil.mp hbs
      subst bs
      exact Or.inr (Or.inl rfl)
  · cases p with
    | nil => exact Or.inl rfl
    | cons b bs =>
      rcases List.cons_prefix_cons.mp hp with ⟨rfl, hbs⟩
      have he := List.prefix_nil.mp hbs
      subst bs
      exact Or.inr (Or.inr rfl)

/-- T2 is a manually constructed positive fixture for the expected merged
cherry. No universal merge transition is claimed by this module. -/
def mergedCherry : Family (.node (.leaf (0 : Nat)) (.leaf 1)) Unit where
  finite := leftSingle.finite
  support := fun _ => withIncursion
  bounded := by
    intro i a ha
    rcases ha with rfl | rfl | rfl <;> trivial
  convex := fun _ => withIncursion_convex
  labelled := fun _ => ⟨[false], 0, ⟨rfl, rfl⟩, Or.inr (Or.inl rfl)⟩
  disjoint := by intro i j a hi hj; cases i; cases j; rfl
  covers := by
    intro a x hx
    cases a with
    | nil => exact False.elim hx
    | cons b bs =>
      cases b with
      | false =>
        have he := hx.1
        subst bs
        exact ⟨(), Or.inr (Or.inl rfl)⟩
      | true =>
        have he := hx.1
        subst bs
        exact ⟨(), Or.inr (Or.inr rfl)⟩
  boundary := some ()
  root_spec := by intro i; cases i; simp [withIncursion]

theorem t2_merged_fixture : mergedCherry.blockCount = 1 ∧ mergedCherry.cost = 0 ∧
    mergedCherry.cost + boundaryCharge mergedCherry.boundary = 1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem regression_incursion_labels :
    (∀ a, a = [false] → (withoutIncursion a ↔ withIncursion a)) ∧
    (¬ withoutIncursion [true]) ∧ withIncursion [true] := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha; subst a; simp [withoutIncursion, withIncursion]
  · simp [withoutIncursion]
  · simp [withIncursion]

#print axioms t2_merged_fixture
#print axioms withIncursion_convex
#print axioms singletonFamily
#print axioms t1_closed_count_cost
#print axioms t1_leaf_owners
#print axioms t3_extensions
#print axioms t4_distinct_labels_same_color
#print axioms t4_adjacent_same_color_separate
#print axioms t5_singleton
#print axioms regression_gap
#print axioms regression_incursion_labels
end TripleDP.CostRoute
