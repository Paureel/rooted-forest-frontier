import Mathlib

namespace RuntimeRepairGeometry

/-- A binary subtree with cut flags on its two child edges. -/
inductive CutTree where
  | leaf
  | branch (cutLeft cutRight : Bool) (left right : CutTree)

def survives : CutTree → Bool
  | .leaf => true
  | .branch l r x y => ((!l) && survives x) || ((!r) && survives y)

def NoSiblingCuts : CutTree → Prop
  | .leaf => True
  | .branch l r x y => (l = false ∨ r = false) ∧ NoSiblingCuts x ∧ NoSiblingCuts y

/-- Exact conditional structural kernel: a protected incoming edge plus
    no simultaneous sibling cuts leaves a descendant in its subtree. -/
theorem surviving_descendant (t : CutTree) (h : NoSiblingCuts t) : survives t = true := by
  induction t with
  | leaf => rfl
  | branch l r x y ihx ihy =>
    obtain ⟨hlr, hx, hy⟩ := h
    have sx := ihx hx
    have sy := ihy hy
    cases hlr with
    | inl hl => simp [survives, hl, sx]
    | inr hr => simp [survives, hr, sy]

/-- Planted negative control: arbitrary simultaneous cuts erase a cherry. -/
theorem both_children_erased : survives (.branch true true .leaf .leaf) = false := by rfl

/-- Integer path-length part of the two-root geometry. -/
theorem oriented_three_pendants (hx hy : Nat)
    (hxpos : 1 ≤ hx) (hypos : 1 ≤ hy)
    (s : hx + hy = 5) (orient : hy ≤ hx) :
    3 ≤ hx ∧ (hy = 1 → hx = 4) := by omega

/-- Pessimistic terminal pair estimate, written at one fixed scale. -/
theorem e2_one_pendant (scale child : ℚ)
    (hchild : child ≤ scale / 4 - 3) : 1 + (1 + child) ≤ scale / 4 - 1 := by linarith

/-- Two legal branches at a protected endpoint: endpoint branch is dead;
    all-pendant branch spends at least two cuts then one final cut. -/
theorem e2_two_or_more (scale child : ℚ) (hs : 8 ≤ scale)
    (hchild : child ≤ scale / 8 - 3) :
    1 + 1 + (1 + child) ≤ scale / 4 - 1 := by linarith

/-- Both active endpoints protected: at least two pendant cuts followed by
    a final outer endpoint cut. -/
theorem both_protected (scale child : ℚ)
    (hchild : child ≤ scale / 8 - 3) :
    1 + (1 + child) ≤ scale / 8 - 1 := by linarith

/-- Four-root uncle, other pair makes three A2BC calls. No cardinality-two cap. -/
theorem four_root_a2 (scale a b c : ℚ)
    (ha : a ≤ scale / 8 - 1) (hb : b ≤ scale / 16 - 1)
    (hc : c ≤ scale / 16 - 1) :
    1 + a + b + c ≤ scale / 4 - 2 := by linarith

/-- Same composition with at least three pendant cuts. -/
theorem four_root_a3 (scale a b c : ℚ) (hs : 0 ≤ scale)
    (ha : a ≤ scale / 8 - 1) (hb : b ≤ scale / 32 - 1)
    (hc : c ≤ scale / 16 - 1) :
    1 + a + b + c ≤ scale / 4 - 2 := by linarith

/-- A one-call rule spending one cut, allowing a free local merger. -/
theorem four_root_single (scale child : ℚ)
    (hc : child ≤ scale / 4 - 2) : 1 + child ≤ scale / 4 - 1 := by linarith

/-- BCY's two calls each spend two cuts, allowing a free local merger. -/
theorem four_root_bcy (scale a b : ℚ)
    (ha : a ≤ scale / 8 - 2) (hb : b ≤ scale / 8 - 2) :
    1 + a + b ≤ scale / 4 - 3 := by linarith

/-- Exact use-site arithmetic for the sufficient C bound. -/
theorem joint_target (scale a b c : ℚ)
    (ha : a ≤ scale / 4 - 2) (hb : b ≤ scale / 8 - 3)
    (hc : c ≤ scale / 8 - 1) :
    1 + a + b + c ≤ scale / 2 - 5 := by linarith

#print axioms surviving_descendant
#print axioms oriented_three_pendants
#print axioms four_root_a2
#print axioms joint_target
end RuntimeRepairGeometry
