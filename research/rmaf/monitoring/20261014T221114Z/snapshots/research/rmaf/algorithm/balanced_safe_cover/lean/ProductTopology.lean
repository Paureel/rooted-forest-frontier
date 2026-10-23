import RMAF

/-! Topology constituents for the restricted private-gadget product family.
These do not prove source-cut realization or arbitrary-input safe-cover generation.
-/
namespace ProductTopology
open RMAF

def sourceGadget (i : Nat) : Tree :=
  .node (.node (.leaf (3*i+1)) (.leaf (3*i+3))) (.leaf (3*i+2))
def targetGadget (i : Nat) : Tree :=
  .node (.node (.leaf (3*i+1)) (.leaf (3*i+2))) (.leaf (3*i+3))
def sourceFamily : Nat → Tree
  | 0 => .leaf 0
  | n+1 => .node (sourceGadget n) (sourceFamily n)
def targetFamily : Nat → Tree
  | 0 => .leaf 0
  | n+1 => .node (targetGadget n) (targetFamily n)

theorem restrictionAgrees_join (s₁ s₂ t₁ t₂ : Tree) (selected : List Nat)
    (h₁ : restrictionAgrees s₁ t₁ selected = true)
    (h₂ : restrictionAgrees s₂ t₂ selected = true) :
    restrictionAgrees (.node s₁ s₂) (.node t₁ t₂) selected = true := by
  unfold restrictionAgrees at h₁ h₂ ⊢
  cases hs₁ : restrict selected s₁ <;> cases ht₁ : restrict selected t₁ <;>
    cases hs₂ : restrict selected s₂ <;> cases ht₂ : restrict selected t₂ <;>
    simp_all [restrict, sameShape]

theorem gadget_after_distinguished_deletion (i : Nat) (selected : List Nat)
    (ha : selected.contains (3*i+1) = false)
    (hb : selected.contains (3*i+2) = true)
    (hc : selected.contains (3*i+3) = true) :
    restrictionAgrees (sourceGadget i) (targetGadget i) selected = true := by
  have ha' : 3*i+1 ∉ selected := by simpa using ha
  have hb' : 3*i+2 ∈ selected := by simpa using hb
  have hc' : 3*i+3 ∈ selected := by simpa using hc
  simp [sourceGadget, targetGadget, restrictionAgrees, restrict, sameShape, ha', hb', hc']

def SelectsRemainder (r : Nat) (selected : List Nat) : Prop :=
  selected.contains 0 = true ∧ ∀ i < r,
    selected.contains (3*i+1) = false ∧
    selected.contains (3*i+2) = true ∧ selected.contains (3*i+3) = true

theorem family_after_distinguished_deletion (r : Nat) (selected : List Nat)
    (h : SelectsRemainder r selected) :
    restrictionAgrees (sourceFamily r) (targetFamily r) selected = true := by
  induction r with
  | zero =>
      have h0 : 0 ∈ selected := by simpa using h.1
      simp [sourceFamily, targetFamily, restrictionAgrees, restrict, sameShape, h0]
  | succ n ih =>
      simp only [sourceFamily, targetFamily]
      apply restrictionAgrees_join
      · have hi := h.2 n (by omega)
        exact gadget_after_distinguished_deletion n selected hi.1 hi.2.1 hi.2.2
      · apply ih
        refine ⟨h.1, ?_⟩
        intro i hi
        exact h.2 i (by omega)

theorem half_gadget_budget (r : Nat) : 2 * (r - (r+1)/2) ≤ r := by omega
theorem chosen_gadgets_affordable (r b : Nat) (h : r ≤ b) : (r+1)/2 ≤ b := by omega
theorem first_full_gadget_incompatible :
    restrictionAgrees (sourceGadget 0) (targetGadget 0) [1,2,3] = false := by decide

#print axioms restrictionAgrees_join
#print axioms gadget_after_distinguished_deletion
#print axioms family_after_distinguished_deletion
#print axioms half_gadget_budget
#print axioms chosen_gadgets_affordable
#print axioms first_full_gadget_incompatible
end ProductTopology
