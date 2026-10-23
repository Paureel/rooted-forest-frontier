import Std

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

/-- Fixed-scale integer arithmetic. Denominators are cleared explicitly;
    scale represents alpha*2^k and bounds on call counts are integral. -/
theorem e2_one_pendant (scale child : Int)
    (hchild : 4*child ≤ scale - 12) : 4*(1 + (1 + child)) ≤ scale - 4 := by omega

theorem e2_two_or_more (scale child : Int) (hs : 8 ≤ scale)
    (hchild : 8*child ≤ scale - 24) :
    4*(1 + 1 + (1 + child)) ≤ scale - 4 := by omega

theorem both_protected (scale child : Int)
    (hchild : 8*child ≤ scale - 24) :
    8*(1 + (1 + child)) ≤ scale - 8 := by omega

theorem four_root_two_endpoints (scale a c : Int)
    (ha : 8*a ≤ scale - 8) (hc : 8*c ≤ scale - 8) :
    4*(1 + a + c) ≤ scale - 4 := by omega

theorem four_root_a2 (scale a b c : Int)
    (ha : 8*a ≤ scale - 8) (hb : 16*b ≤ scale - 16)
    (hc : 16*c ≤ scale - 16) :
    4*(1 + a + b + c) ≤ scale - 8 := by omega

theorem four_root_a3 (scale a b c : Int) (hs : 0 ≤ scale)
    (ha : 8*a ≤ scale - 8) (hb : 32*b ≤ scale - 32)
    (hc : 16*c ≤ scale - 16) :
    4*(1 + a + b + c) ≤ scale - 8 := by omega

theorem four_root_single (scale child : Int)
    (hc : 4*child ≤ scale - 8) : 4*(1 + child) ≤ scale - 4 := by omega

theorem four_root_bcy (scale a b : Int)
    (ha : 8*a ≤ scale - 16) (hb : 8*b ≤ scale - 16) :
    4*(1 + a + b) ≤ scale - 12 := by omega

theorem joint_target (scale a b c : Int)
    (ha : 4*a ≤ scale - 8) (hb : 8*b ≤ scale - 24)
    (hc : 8*c ≤ scale - 8) :
    2*(1 + a + b + c) ≤ scale - 10 := by omega

def ternaryBound : Nat → Nat
  | 0 => 4
  | n+1 => 1 + 3 * ternaryBound n

theorem small_budget_allowances :
    1 ≤ 15 ∧ ternaryBound 0 ≤ 31 ∧ ternaryBound 1 ≤ 63 ∧
    ternaryBound 2 ≤ 127 ∧ ternaryBound 3 ≤ 255 := by decide

#print axioms surviving_descendant
#print axioms oriented_three_pendants
#print axioms four_root_a2
#print axioms joint_target
end RuntimeRepairGeometry

#print axioms RuntimeRepairGeometry.surviving_descendant
#print axioms RuntimeRepairGeometry.both_children_erased
#print axioms RuntimeRepairGeometry.oriented_three_pendants
#print axioms RuntimeRepairGeometry.e2_one_pendant
#print axioms RuntimeRepairGeometry.e2_two_or_more
#print axioms RuntimeRepairGeometry.both_protected
#print axioms RuntimeRepairGeometry.four_root_two_endpoints
#print axioms RuntimeRepairGeometry.four_root_a2
#print axioms RuntimeRepairGeometry.four_root_a3
#print axioms RuntimeRepairGeometry.four_root_single
#print axioms RuntimeRepairGeometry.four_root_bcy
#print axioms RuntimeRepairGeometry.joint_target
#print axioms RuntimeRepairGeometry.small_budget_allowances
