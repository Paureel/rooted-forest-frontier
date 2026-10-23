import PathStem
/- One-shot finite controls frozen in WORK.md. No census; no held-out claim. -/
namespace TripleDP.PathRoute.Controls

instance (a b v : Address) : Decidable (OnPath a b v) :=
  inferInstanceAs (Decidable (lca a b <+: v ∧ (v <+: a ∨ v <+: b)))

def T : BTree Nat := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def T2 : BTree Nat := .node (.leaf 0) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
def leaves (t : BTree Nat) : List Address := (leafEntries t).map Prod.fst

def trim (t : BTree Nat) (r : List Address) : List Address :=
  (vertices t).filter fun v => (leaves t).any fun a => decide (a ∈ r ∧ v <+: a)

def convex (t : BTree Nat) (r : List Address) : Bool :=
  r.all fun a => r.all fun b =>
    (vertices t).all fun v => decide (OnPath a b v → v ∈ r)

def lcaClosed (r : List Address) : Bool :=
  r.all fun a => r.all fun b => decide (lca a b ∈ r)

def disjoint (a b : List Address) : Bool :=
  a.all fun v => decide (v ∉ b)

def R0 : List Address := [[], [false], [false, false]]
def R1 : List Address := [[], [false], [false, false], [true]]
def G : List Address := [[], [false, false]]
def R2 : List Address := [[], [true], [true, false], [true, false, false], [true, true], [false]]
def R3 : List Address := [[], [true], [true, false], [true, false, false], [true, true]]

theorem t_vertices : vertices T =
    [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide

theorem known_incursion_pair :
    convex T R0 = true ∧ convex T R1 = true ∧
    trim T R0 = R0 ∧ trim T R1 = R0 ∧ [true] ∉ trim T R1 := by decide

theorem known_gap : lcaClosed G = true ∧ convex T G = false := by decide

theorem independent_asymmetric_pair :
    leaves T2 = [[false], [true, false, false], [true, false, true], [true, true]] ∧
    convex T2 R2 = true ∧ convex T2 R3 = true ∧
    trim T2 R2 = [[], [false], [true], [true, false], [true, false, false], [true, true]] ∧
    trim T2 R3 = R3 ∧ [false] ∈ trim T2 R2 ∧ [false] ∉ trim T2 R3 := by decide

theorem root_singleton_boundary : trim (.leaf 9) [[]] = [[]] := by decide

theorem empty_label_boundary : trim T [[]] = [] := by decide

/-- The two adjacent same-color supports have separate indices, before and
following the displayed shrinking. No connected-component merging occurs. -/
theorem adjacent_same_color_and_unused :
    let before : List (List Address) := [[[false], [false, false]], [[false, true]]]
    let after : List (List Address) := [[[false, false]], [[false, true]]]
    let colors : List Nat := [0, 0]
    before.length = 2 ∧ after.length = 2 ∧ colors = [0, 0] ∧
    disjoint before[0]! before[1]! = true ∧ disjoint after[0]! after[1]! = true ∧
    [true] ∉ before.flatten ∧ [true] ∈ vertices T := by decide

#print axioms t_vertices
#print axioms known_incursion_pair
#print axioms known_gap
#print axioms independent_asymmetric_pair
#print axioms root_singleton_boundary
#print axioms empty_label_boundary
#print axioms adjacent_same_color_and_unused
end TripleDP.PathRoute.Controls
