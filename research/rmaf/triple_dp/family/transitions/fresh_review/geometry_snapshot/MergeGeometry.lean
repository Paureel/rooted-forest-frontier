import GeometrySupportDefs

/-! Problem-specific independent universal support geometry. The proof route
is first-edge decomposition and prefix/root-path closure. This file contains
no enumeration, index deletion, block-count, or cost calculation. -/
namespace TripleDP.GeometryRoute
open TripleDP TripleDP.CostRoute
variable {α I J : Type}

@[simp] theorem jointSupport_root (s t : Address → Prop) : jointSupport s t [] := by
  trivial

@[simp] theorem jointSupport_left (s t : Address → Prop) (a : Address) :
    jointSupport s t (false :: a) ↔ s a := Iff.rfl

@[simp] theorem jointSupport_right (s t : Address → Prop) (a : Address) :
    jointSupport s t (true :: a) ↔ t a := Iff.rfl

/-- Exact interface to the required root-and-two-lifts support. -/
theorem jointSupport_union (s t : Address → Prop) (a : Address) :
    jointSupport s t a ↔
      a = [] ∨ liftSupport false s a ∨ liftSupport true t a := by
  cases a with
  | nil => simp [jointSupport]
  | cons b as => cases b <;> simp [jointSupport, liftSupport]

/-- Prefix closure follows by inspecting the first edge of an address. -/
theorem jointSupport_prefixClosed (s t : Address → Prop)
    (hs : PrefixClosed s) (ht : PrefixClosed t) :
    PrefixClosed (jointSupport s t) := by
  intro a ha p hp
  cases p with
  | nil => trivial
  | cons b ps =>
    cases a with
    | nil => cases List.prefix_nil.mp hp
    | cons c as =>
      rcases List.cons_prefix_cons.mp hp with ⟨rfl, htail⟩
      cases b with
      | false => exact hs as ha ps htail
      | true => exact ht as ha ps htail

/-- Both child roots are required to turn child convexity into prefix closure. -/
theorem jointSupport_convex (s t : Address → Prop)
    (hs : PathConvex s) (ht : PathConvex t) (sr : s []) (tr : t []) :
    PathConvex (jointSupport s t) := by
  apply (rooted_pathConvex_iff_prefixClosed _ (jointSupport_root s t)).mpr
  exact jointSupport_prefixClosed s t
    ((rooted_pathConvex_iff_prefixClosed s sr).mp hs)
    ((rooted_pathConvex_iff_prefixClosed t tr).mp ht)

/-- A genuinely geometric root-path presentation: all root-to-child-support
paths, with no finite-index or deletion operation. -/
def rootPathUnion (s t : Address → Prop) (a : Address) : Prop :=
  (∃ b, s b ∧ a <+: false :: b) ∨ (∃ b, t b ∧ a <+: true :: b)

theorem jointSupport_rootPaths (s t : Address → Prop)
    (hs : PrefixClosed s) (ht : PrefixClosed t) (sr : s []) (a : Address) :
    jointSupport s t a ↔ rootPathUnion s t a := by
  constructor
  · intro ha
    cases a with
    | nil => exact Or.inl ⟨[], sr, by simp⟩
    | cons b as =>
      cases b with
      | false => exact Or.inl ⟨as, ha, List.prefix_rfl⟩
      | true => exact Or.inr ⟨as, ha, List.prefix_rfl⟩
  · intro ha
    rcases ha with ⟨b, hb, hp⟩ | ⟨b, hb, hp⟩
    · exact jointSupport_prefixClosed s t hs ht (false :: b) hb a hp
    · exact jointSupport_prefixClosed s t hs ht (true :: b) hb a hp

/-- Actual BTree vertex boundedness, not abstract address boundedness. -/
theorem jointSupport_bounded {l r : BTree α} (s t : Address → Prop)
    (hs : ∀ a, s a → Vertex l a) (ht : ∀ a, t a → Vertex r a) :
    ∀ a, jointSupport s t a → Vertex (.node l r) a := by
  intro a ha
  cases a with
  | nil => trivial
  | cons b as => cases b with
    | false => exact hs as ha
    | true => exact ht as ha

/-- Exact leaf-label union; repeated values of labels are allowed. -/
theorem jointSupport_labels {l r : BTree α} (s t : Address → Prop) (x : α) :
    (∃ a, LeafAt (.node l r) a x ∧ jointSupport s t a) ↔
      (∃ a, LeafAt l a x ∧ s a) ∨ (∃ a, LeafAt r a x ∧ t a) := by
  constructor
  · rintro ⟨a, hx, ha⟩
    cases a with
    | nil => exact False.elim hx
    | cons b as => cases b with
      | false => exact Or.inl ⟨as, hx, ha⟩
      | true => exact Or.inr ⟨as, hx, ha⟩
  · intro h
    rcases h with ⟨a, hx, ha⟩ | ⟨a, hx, ha⟩
    · exact ⟨false :: a, hx, ha⟩
    · exact ⟨true :: a, hx, ha⟩

/-- A disjoint child support remains disjoint from the whole merged support. -/
theorem jointSupport_disjoint_left (s t u : Address → Prop)
    (hsu : ∀ a, s a → u a → False) :
    ∀ a, jointSupport s t a → liftSupport false u a → False := by
  intro a ha hu
  cases a with
  | nil => exact hu
  | cons b as =>
    rcases hu with ⟨rfl, hu⟩
    exact hsu as ha hu

theorem jointSupport_disjoint_right (s t u : Address → Prop)
    (htu : ∀ a, t a → u a → False) :
    ∀ a, jointSupport s t a → liftSupport true u a → False := by
  intro a ha hu
  cases a with
  | nil => exact hu
  | cons b as =>
    rcases hu with ⟨rfl, hu⟩
    exact htu as ha hu

/-- The interface consumed by a future finite-index merge constructor. -/
def familyJoint {l r : BTree α} (f : Family l I) (g : Family r J)
    (i : I) (j : J) : Address → Prop := jointSupport (f.support i) (g.support j)

theorem familyJoint_convex {l r : BTree α} (f : Family l I) (g : Family r J)
    (i : I) (j : J) (hi : f.boundary = some i) (hj : g.boundary = some j) :
    PathConvex (familyJoint f g i j) :=
  jointSupport_convex _ _ (f.convex i) (g.convex j)
    ((f.root_spec i).mpr hi) ((g.root_spec j).mpr hj)

theorem familyJoint_bounded {l r : BTree α} (f : Family l I) (g : Family r J)
    (i : I) (j : J) : ∀ a, familyJoint f g i j a → Vertex (.node l r) a :=
  jointSupport_bounded _ _ (f.bounded i) (g.bounded j)

theorem familyJoint_labels {l r : BTree α} (f : Family l I) (g : Family r J)
    (i : I) (j : J) (x : α) :
    (∃ a, LeafAt (.node l r) a x ∧ familyJoint f g i j a) ↔
      f.hasLabel i x ∨ g.hasLabel j x := jointSupport_labels _ _ x

theorem familyJoint_labelled {l r : BTree α} (f : Family l I) (g : Family r J)
    (i : I) (j : J) : ∃ a x, LeafAt (.node l r) a x ∧ familyJoint f g i j a := by
  rcases f.labelled i with ⟨a, x, hx, hi⟩
  exact ⟨false :: a, x, hx, hi⟩

theorem familyJoint_disjoint_left {l r : BTree α} (f : Family l I) (g : Family r J)
    (i k : I) (j : J) (hik : i ≠ k) :
    ∀ a, familyJoint f g i j a → liftSupport false (f.support k) a → False :=
  jointSupport_disjoint_left _ _ _ (fun a hi hk => hik (f.disjoint i k a hi hk))

theorem familyJoint_disjoint_right {l r : BTree α} (f : Family l I) (g : Family r J)
    (i : I) (j k : J) (hjk : j ≠ k) :
    ∀ a, familyJoint f g i j a → liftSupport true (g.support k) a → False :=
  jointSupport_disjoint_right _ _ _ (fun a hj hk => hjk (g.disjoint j k a hj hk))

#print axioms jointSupport_root
#print axioms jointSupport_left
#print axioms jointSupport_right
#print axioms jointSupport_union
#print axioms jointSupport_prefixClosed
#print axioms jointSupport_convex
#print axioms jointSupport_rootPaths
#print axioms jointSupport_bounded
#print axioms jointSupport_labels
#print axioms jointSupport_disjoint_left
#print axioms jointSupport_disjoint_right
#print axioms familyJoint_convex
#print axioms familyJoint_bounded
#print axioms familyJoint_labels
#print axioms familyJoint_labelled
#print axioms familyJoint_disjoint_left
#print axioms familyJoint_disjoint_right
end TripleDP.GeometryRoute
