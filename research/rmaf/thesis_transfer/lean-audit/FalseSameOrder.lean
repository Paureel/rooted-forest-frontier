import RMAF

/-! Local structural lemmas for the opposite-caterpillar reduction.
These do not prove the whole AF transport theorem. RMAF's rho-leaf encoding
is used only for these structural lemmas; the Python oracle uses the thesis's
unary labelled-root rho. Their equivalence is documented, not formalized here.
-/
namespace ThesisTransfer
open RMAF

def graft (outer inner : Nat) (t : Tree) : Tree :=
  .node (.leaf outer) (.node (.leaf inner) t)

def augment (rho : Nat) (t : Tree) : Tree := .node (.leaf rho) t

/-- Any block meeting both new leaves and the original subtree disagrees
between the two opposite orders. This is a direct restriction calculation. -/
theorem two_markers_disagree (a b rho : Nat) (s : List Nat)
    (t u rt ru : Tree) (hab : a ≠ b)
    (ha : s.contains a = true) (hb : s.contains b = true)
    (ht : restrict s t = some rt) (hu : restrict s u = some ru) :
    restrictionAgrees (augment rho (graft b a t))
      (augment rho (graft b a u)) s = false := by
  have hba : (b == a) = false := by simp [Ne.symm hab]
  have habb : (a == b) = false := by simp [hab]
  cases hr : s.contains rho <;>
    simp_all [restrictionAgrees, augment, graft, restrict, sameShape]

/-- The root of a nonempty rooted span is retained. -/
theorem rootedSpan_head (s : List Nat) (t : Tree)
    (h : (rootedSpan s t).isEmpty = false) :
    [] ∈ rootedSpan s t := by
  cases t with
  | leaf x =>
      cases hx : s.contains x <;> simp_all [rootedSpan]
  | node l r =>
      simp only [rootedSpan] at h ⊢
      split at h <;> simp_all

/-- A selected leaf forces a nonempty rooted span; LCA positions are not assumed. -/
theorem rootedSpan_nonempty_of_leaf (s : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hs : s.contains x = true) :
    (rootedSpan s t).isEmpty = false := by
  induction t with
  | leaf y =>
      have he : x = y := by simpa [leaves] using hx
      subst y
      simp_all [rootedSpan]
  | node l r hl hr =>
      rcases List.mem_append.mp hx with hx | hx
      · have hh := hl hx
        simp [rootedSpan, hh]
      · have hh := hr hx
        simp [rootedSpan, hh]

/-- With an inner marker selected, the original subtree root lies in the
minimal embedding, even though it may lie above that block's old-leaf LCA. -/
theorem old_root_mem_inner (outer inner rho : Nat) (s : List Nat) (t : Tree)
    (hin : s.contains inner = true)
    (ht : (rootedSpan s t).isEmpty = false) :
    [true,true,true] ∈ minimalVertices s (augment rho (graft outer inner t)) := by
  have hm := rootedSpan_head s t ht
  cases ho : s.contains outer <;> cases hr : s.contains rho <;>
    simp_all [minimalVertices, rootedSpan, augment, graft, prependSide]

/-- Same root obstruction for an outer marker. -/
theorem old_root_mem_outer (outer inner rho : Nat) (s : List Nat) (t : Tree)
    (hout : s.contains outer = true)
    (ht : (rootedSpan s t).isEmpty = false) :
    [true,true,true] ∈ minimalVertices s (augment rho (graft outer inner t)) := by
  have hm := rootedSpan_head s t ht
  cases hi : s.contains inner <;> cases hr : s.contains rho <;>
    simp_all [minimalVertices, rootedSpan, augment, graft, prependSide]

/-- The rho marker has the same obstruction in the binary-leaf encoding. -/
theorem old_root_mem_rho (outer inner rho : Nat) (s : List Nat) (t : Tree)
    (hrho : s.contains rho = true)
    (ht : (rootedSpan s t).isEmpty = false) :
    [true,true,true] ∈ minimalVertices s (augment rho (graft outer inner t)) := by
  have hm := rootedSpan_head s t ht
  cases hi : s.contains inner <;> cases ho : s.contains outer <;>
    simp_all [minimalVertices, rootedSpan, augment, graft, prependSide]

/-- A shared vertex contradicts the actual Boolean disjointness predicate. -/
theorem shared_vertex_not_disjoint (xs ys : List Vertex) (v : Vertex)
    (hx : v ∈ xs) (hy : v ∈ ys) : disjointVertices xs ys = false := by
  simp only [disjointVertices]
  apply Bool.eq_false_iff.mpr
  intro h
  have hh := List.all_eq_true.mp h v hx
  have hc : ys.contains v = true := List.contains_iff_mem.mpr hy
  simp [hy] at hh

/-- Every mixed block traverses the same original subtree root. -/
theorem old_root_mem_mixed (outer inner rho : Nat) (s : List Nat) (t : Tree)
    (ht : (rootedSpan s t).isEmpty = false)
    (hm : s.contains outer = true ∨ s.contains inner = true ∨
      s.contains rho = true) :
    [true,true,true] ∈ minimalVertices s (augment rho (graft outer inner t)) := by
  rcases hm with ho | hi | hr
  · exact old_root_mem_outer outer inner rho s t ho ht
  · exact old_root_mem_inner outer inner rho s t hi ht
  · exact old_root_mem_rho outer inner rho s t hr ht

/-- Two mixed blocks cannot be distinct vertex-disjoint components. -/
theorem mixed_blocks_overlap (outer inner rho : Nat) (s z : List Nat) (t : Tree)
    (hs : (rootedSpan s t).isEmpty = false)
    (hz : (rootedSpan z t).isEmpty = false)
    (hsm : s.contains outer = true ∨ s.contains inner = true ∨ s.contains rho = true)
    (hzm : z.contains outer = true ∨ z.contains inner = true ∨ z.contains rho = true) :
    disjointVertices (minimalVertices s (augment rho (graft outer inner t)))
      (minimalVertices z (augment rho (graft outer inner t))) = false := by
  apply shared_vertex_not_disjoint _ _ [true,true,true]
  · exact old_root_mem_mixed outer inner rho s t hs hsm
  · exact old_root_mem_mixed outer inner rho z t hz hzm

/-- Quantified arithmetic interface only: the graph maps must be supplied.
It is deliberately not advertised as unconditional MAF correctness. -/
theorem optimum_shift_from_maps (Old New : Type)
    (oldOK : Old → Prop) (newOK : New → Prop)
    (oldCost : Old → Nat) (newCost : New → Nat)
    (k kg : Nat)
    (oldMin : (∃ x, oldOK x ∧ oldCost x = k) ∧
      ∀ x, oldOK x → k ≤ oldCost x)
    (newMin : (∃ x, newOK x ∧ newCost x = kg) ∧
      ∀ x, newOK x → kg ≤ newCost x)
    (lift : ∀ x, oldOK x → ∃ y, newOK y ∧ newCost y = oldCost x + 1)
    (erase : ∀ y, newOK y → ∃ x, oldOK x ∧ oldCost x + 1 ≤ newCost y) :
    kg = k + 1 := by
  obtain ⟨x, hx, hxc⟩ := oldMin.1
  obtain ⟨y, hy, hyc⟩ := lift x hx
  have hupper := newMin.2 y hy
  obtain ⟨z, hz, hzc⟩ := newMin.1
  obtain ⟨w, hw, hwc⟩ := erase z hz
  have hlower := oldMin.2 w hw
  omega

theorem cuts_equal_components (k kg : Nat) (h : kg = k+1) : kg-1 = k := by omega

#print axioms two_markers_disagree
#print axioms rootedSpan_head
#print axioms rootedSpan_nonempty_of_leaf
#print axioms old_root_mem_inner
#print axioms old_root_mem_outer
#print axioms old_root_mem_rho
#print axioms shared_vertex_not_disjoint
#print axioms old_root_mem_mixed
#print axioms mixed_blocks_overlap
#print axioms optimum_shift_from_maps
#print axioms cuts_equal_components
end ThesisTransfer
