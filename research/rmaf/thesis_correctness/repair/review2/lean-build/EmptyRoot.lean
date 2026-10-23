import Std

/- A local finite combinatorial certificate, NOT a formalization of AF
   compatibility or of the global normalization theorem. Each leaf carries
   a label, every internal endpoint node is binary, and each Bool records
   whether the corresponding child edge was cut. -/
namespace ComponentRepair

inductive CutTree where
  | leaf : CutTree
  | fork (cutLeft : Bool) (left : CutTree)
      (cutRight : Bool) (right : CutTree) : CutTree
  deriving Repr

def edgeCost (cut : Bool) : Nat := if cut then 1 else 0

def cutCount : CutTree → Nat
  | .leaf => 0
  | .fork cl l cr r => edgeCost cl + cutCount l + edgeCost cr + cutCount r

def survives : CutTree → Prop
  | .leaf => True
  | .fork cl l cr r => (cl = false ∧ survives l) ∨ (cr = false ∧ survives r)

def restore : CutTree → CutTree
  | .leaf => .leaf
  | .fork _ l _ r => .fork false (restore l) false (restore r)

theorem restored_alive (t : CutTree) : survives (restore t) := by
  induction t with
  | leaf => trivial
  | fork cl l cr r ihl ihr =>
      exact Or.inl ⟨rfl, ihl⟩

theorem restored_no_internal_cuts (t : CutTree) : cutCount (restore t) = 0 := by
  induction t with
  | leaf => rfl
  | fork cl l cr r ihl ihr => simp [restore, cutCount, edgeCost, ihl, ihr]

/- The two child branches are disjoint. Blocking both requires at least two
   internal cuts, even if cuts occur well below the root's child edges. -/
theorem empty_root_needs_two_cuts (t : CutTree) (h : ¬ survives t) :
    2 ≤ cutCount t := by
  induction t with
  | leaf => exact False.elim (h True.intro)
  | fork cl l cr r ihl ihr =>
      have hl : cl = false → ¬ survives l := by
        intro hcl live
        exact h (Or.inl ⟨hcl, live⟩)
      have hr : cr = false → ¬ survives r := by
        intro hcr live
        exact h (Or.inr ⟨hcr, live⟩)
      cases cl <;> cases cr <;> simp_all [cutCount, edgeCost] <;> omega

/- Restoring the entire proper pendant subtree and cutting its incoming
   edge costs one locally. Even allowing that incoming edge to have already
   been cut, an emptied root costs strictly more. The separate prose proof
   must establish that this replacement is an AF before invoking optimality. -/
theorem empty_root_repair_strict (t : CutTree) (outside : Nat)
    (incomingWasCut : Bool) (h : ¬ survives t) :
    outside + 1 < outside + cutCount t + edgeCost incomingWasCut := by
  have hh := empty_root_needs_two_cuts t h
  omega

/- Exact planted boundary: two cuts are sufficient, so replacing the lower
   bound 2 by 3 is false. -/
example : cutCount (.fork true .leaf true .leaf) = 2 := by decide
example : ¬ survives (.fork true .leaf true .leaf) := by simp [survives]

#print axioms restored_alive
#print axioms restored_no_internal_cuts
#print axioms empty_root_needs_two_cuts
#print axioms empty_root_repair_strict

/- Two-exchange local accounting. p counts already-cut pendant edges, s
   counts first-path cuts, q counts existing uncle-pair cuts, delta is the
   first incoming-edge insertion, r the resulting uncle-pair cut count,
   and epsilon the second incoming-edge insertion. These are exact Nat
   counts, and the hypotheses describe the branch conditions of the rule. -/
theorem two_exchange_savings (p s q delta r epsilon : Nat)
    (hs : 1 ≤ s) (hselected : 2 ≤ p + s + q)
    (hdelta : delta ≤ 1) (hdeltaOne : s = 1 → delta = 0)
    (hr : r = q + delta) (hepsilon : epsilon ≤ 1)
    (hepsilonSmall : r ≤ 1 → epsilon = 0) :
    2 + delta + epsilon ≤ p + s + r := by
  omega

theorem two_exchange_cost_nonincrease
    (original final p s q delta r epsilon : Nat)
    (hs : 1 ≤ s) (hselected : 2 ≤ p + s + q)
    (hdelta : delta ≤ 1) (hdeltaOne : s = 1 → delta = 0)
    (hr : r = q + delta) (hepsilon : epsilon ≤ 1)
    (hepsilonSmall : r ≤ 1 → epsilon = 0)
    (hcost : final + p + s + r = original + 2 + delta + epsilon) :
    final ≤ original := by
  have hh := two_exchange_savings p s q delta r epsilon hs hselected
    hdelta hdeltaOne hr hepsilon hepsilonSmall
  omega

#print axioms two_exchange_savings
#print axioms two_exchange_cost_nonincrease
end ComponentRepair
