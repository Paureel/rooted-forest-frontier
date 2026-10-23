import TripleDP

/-! Path-convex regions on binary-tree addresses. These statements close a
single-region assembly step, not the cost-preserving family theorem G2. -/
namespace TripleDP

def OnPath (a b v : Address) : Prop :=
  lca a b <+: v ∧ (v <+: a ∨ v <+: b)

def PathConvex (region : Address → Prop) : Prop :=
  ∀ a b, region a → region b → ∀ v, OnPath a b v → region v

def PrefixClosed (region : Address → Prop) : Prop :=
  ∀ a, region a → ∀ p, p <+: a → region p

theorem lca_prefix_left (a b : Address) : lca a b <+: a := by
  induction a generalizing b with
  | nil => simp [lca]
  | cons x xs ih =>
      cases b with
      | nil => simp [lca]
      | cons y ys =>
          by_cases h : x = y
          · subst y
            simpa [lca] using ih ys
          · simp [lca, h]

theorem pathConvex_lca_closed (region : Address → Prop)
    (h : PathConvex region) : LCAClosed region := by
  intro a b ha hb
  exact h a b ha hb (lca a b) ⟨List.prefix_rfl, Or.inl (lca_prefix_left a b)⟩

theorem rooted_pathConvex_iff_prefixClosed (region : Address → Prop)
    (root : region []) : PathConvex region ↔ PrefixClosed region := by
  constructor
  · intro h a ha p hp
    exact h [] a root ha p ⟨by simp [lca], Or.inr hp⟩
  · intro h a b ha hb v hv
    rcases hv.2 with hv | hv
    · exact h a ha v hv
    · exact h b hb v hv

theorem pathConvex_child_restriction (region : Address → Prop)
    (h : PathConvex region) (side : Bool) :
    PathConvex (fun a => region (side :: a)) := by
  intro a b ha hb v hv
  apply h (side :: a) (side :: b) ha hb (side :: v)
  simpa [OnPath, lca] using hv

theorem rooted_child_contains_root (region : Address → Prop)
    (h : PathConvex region) (root : region []) (side : Bool) :
    (∃ a, region (side :: a)) → region [side] := by
  rintro ⟨a, ha⟩
  exact (rooted_pathConvex_iff_prefixClosed region root).mp h
    (side :: a) ha [side] (by simp)

/-- A root-containing region is path convex exactly when its occupied child
restrictions are path convex and include their child roots. This supplies
both directions for joining or extending a single open region. -/
theorem rooted_region_decomposition (region : Address → Prop)
    (root : region []) :
    PathConvex region ↔ ∀ side : Bool,
      PathConvex (fun a => region (side :: a)) ∧
      ((∃ a, region (side :: a)) → region [side]) := by
  constructor
  · intro h side
    exact ⟨pathConvex_child_restriction region h side,
      rooted_child_contains_root region h root side⟩
  · intro h
    apply (rooted_pathConvex_iff_prefixClosed region root).mpr
    intro a ha p hp
    cases a with
    | nil => simpa using (List.prefix_nil.mp hp) ▸ root
    | cons side rest =>
        cases p with
        | nil => exact root
        | cons other tail =>
            rcases List.cons_prefix_cons.mp hp with ⟨heq, htail⟩
            subst other
            have childRoot := (h side).2 ⟨rest, ha⟩
            exact (rooted_pathConvex_iff_prefixClosed
              (fun v => region (side :: v)) childRoot).mp (h side).1
              rest ha tail htail

/-- The adversarial support from the verifier is LCA closed but has a gap.
LCA closure alone cannot replace connected-region semantics. -/
def gappedRegion (a : Address) : Prop := a = [] ∨ a = [false, false]

theorem gapped_region_lca_closed : LCAClosed gappedRegion := by
  intro a b ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [gappedRegion, lca]

theorem gapped_region_not_pathConvex : ¬ PathConvex gappedRegion := by
  intro h
  have hc := (rooted_pathConvex_iff_prefixClosed gappedRegion
    (Or.inl rfl)).mp h [false, false] (Or.inr rfl) [false] (by simp)
  simp [gappedRegion] at hc

#print axioms lca_prefix_left
#print axioms pathConvex_lca_closed
#print axioms rooted_pathConvex_iff_prefixClosed
#print axioms pathConvex_child_restriction
#print axioms rooted_child_contains_root
#print axioms rooted_region_decomposition
#print axioms gapped_region_lca_closed
#print axioms gapped_region_not_pathConvex
end TripleDP
