import NormalizedRestriction

/-! Exact planted raw-family control: all three leaf values coincide, while
the two closed indices remain distinct and the open right incursion is leafless. -/
namespace TripleDP.Transitions.Restriction.NormalizedRoute.Controls
open TripleDP.Family TripleDP.CostRoute

def tree : BTree Nat := .node (.leaf 7) (.node (.leaf 7) (.leaf 7))
def incursion (v : Address) : Prop := v = [] ∨ v = [false] ∨ v = [true]
def closedLeaf (i : Fin 2) : Address := if i = 0 then [true, false] else [true, true]

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hi := i.isLt
  omega

theorem lca_self (a : Address) : lca a a = a := by
  induction a with
  | nil => rfl
  | cons side rest ih => simp [lca, ih]

theorem singleton_convex (a : Address) : PathConvex (fun v => v = a) := by
  intro b c hb hc v hv
  subst b; subst c
  have below : a <+: v := by simpa [lca_self] using hv.1
  rcases hv.2 with above | above
  · exact above.eq_of_length_le below.length_le
  · exact above.eq_of_length_le below.length_le

theorem incursion_convex : PathConvex incursion := by
  apply (rooted_pathConvex_iff_prefixClosed incursion (Or.inl rfl)).mpr
  intro a ha p hp
  rcases ha with rfl | rfl | rfl
  · exact Or.inl (List.prefix_nil.mp hp)
  · cases p with
    | nil => exact Or.inl rfl
    | cons side rest =>
      rcases List.cons_prefix_cons.mp hp with ⟨rfl, h⟩
      have he := List.prefix_nil.mp h
      subst rest
      exact Or.inr (Or.inl rfl)
  · cases p with
    | nil => exact Or.inl rfl
    | cons side rest =>
      rcases List.cons_prefix_cons.mp hp with ⟨rfl, h⟩
      have he := List.prefix_nil.mp h
      subst rest
      exact Or.inr (Or.inr rfl)

theorem tree_leaf_cases (a : Address) (h : Leaf tree a) :
    a = [false] ∨ a = [true, false] ∨ a = [true, true] := by
  cases a with
  | nil => simp [Leaf, tree, label] at h
  | cons side rest =>
    cases side with
    | false =>
      cases rest with
      | nil => exact Or.inl rfl
      | cons b bs => simp [Leaf, tree, label] at h
    | true =>
      cases rest with
      | nil => simp [Leaf, tree, label] at h
      | cons inner tail =>
        cases inner <;> cases tail with
        | nil => simp
        | cons b bs => simp [Leaf, tree, label] at h

def raw : RawFamily tree 2 where
  closed := fun i v => v = closedLeaf i
  openRegion := some incursion
  closed_convex := fun i => singleton_convex (closedLeaf i)
  closed_inside := by
    intro i v hv
    subst v
    rcases fin2_cases i with rfl | rfl <;> simp [closedLeaf, tree, vertex]
  closed_live := by
    intro i
    refine ⟨closedLeaf i, ?_, rfl⟩
    rcases fin2_cases i with rfl | rfl <;>
      exact ⟨7, by simp [closedLeaf, tree, label]⟩
  closed_root := by
    intro i
    rcases fin2_cases i with rfl | rfl <;> simp [closedLeaf]
  closed_disjoint := by
    intro i j v hi hj
    rcases fin2_cases i with rfl | rfl <;>
      rcases fin2_cases j with rfl | rfl <;> simp_all [closedLeaf]
  open_convex := by
    intro R hR
    have he : incursion = R := Option.some.inj hR
    subst R
    exact incursion_convex
  open_inside := by
    intro R hR v hv
    have he : incursion = R := Option.some.inj hR
    subst R
    rcases hv with rfl | rfl | rfl <;> trivial
  open_root := by
    intro R hR
    have he : incursion = R := Option.some.inj hR
    subst R
    exact Or.inl rfl
  open_disjoint := by
    intro R hR i v hv hi
    have he : incursion = R := Option.some.inj hR
    subst R
    subst v
    rcases fin2_cases i with rfl | rfl <;> simp [incursion, closedLeaf] at hv
  covers := by
    intro v hv
    rcases tree_leaf_cases v hv with rfl | rfl | rfl
    · exact Or.inr ⟨incursion, rfl, Or.inr (Or.inl rfl)⟩
    · exact Or.inl ⟨0, by simp [closedLeaf]⟩
    · exact Or.inl ⟨1, by simp [closedLeaf]⟩

theorem raw_live : HasLeaf tree incursion :=
  ⟨[false], ⟨7, rfl⟩, Or.inr (Or.inl rfl)⟩

def assembled := toOpenAssembly raw incursion rfl raw_live

theorem raw_occupied_right : ∃ a, assembled.support (.inr ()) (true :: a) :=
  ⟨[], Or.inr (Or.inr rfl)⟩

theorem raw_no_right_leaf : ¬ Live assembled true (.inr ()) := by
  rintro ⟨a, x, leaf, support⟩
  change incursion (true :: a) at support
  have he : a = [] := by simpa [incursion] using support
  subst a
  exact leaf

theorem raw_not_openBranchLive : ¬ OpenBranchLive assembled := by
  intro h
  exact raw_no_right_leaf (h (.inr ()) rfl true raw_occupied_right)

theorem rooted_convex_leaf_does_not_suffice :
    PathConvex incursion ∧ HasLeaf tree incursion ∧ incursion [] ∧
    (∃ a, assembled.support (.inr ()) (true :: a)) ∧
    ¬ Live assembled true (.inr ()) :=
  ⟨incursion_convex, raw_live, Or.inl rfl, raw_occupied_right, raw_no_right_leaf⟩

theorem normalized_retains :
    (normalize raw).openRegion = some (OpenHull tree incursion) :=
  trimOpen_live tree incursion raw_live

theorem normalized_satisfies :
    OpenBranchLive (toOpenAssembly (normalize raw) (OpenHull tree incursion)
      normalized_retains (normalize_retained raw _ normalized_retains)) :=
  normalized_open_openBranchLive raw _ normalized_retains _

theorem normalized_no_right_incursion :
    ∀ a, ¬ (OpenHull tree incursion) (true :: a) := by
  apply normalized_open_no_leafless_child raw _ normalized_retains true
  rintro ⟨a, leaf, support⟩
  have oldSupport := openHull_subset tree incursion incursion_convex
    (Or.inl rfl) (true :: a) support
  have he : a = [] := by simpa [incursion] using oldSupport
  subst a
  simp [Leaf, tree, label] at leaf

#print axioms raw
#print axioms raw_occupied_right
#print axioms raw_no_right_leaf
#print axioms raw_not_openBranchLive
#print axioms rooted_convex_leaf_does_not_suffice
#print axioms normalized_retains
#print axioms normalized_satisfies
#print axioms normalized_no_right_incursion
end TripleDP.Transitions.Restriction.NormalizedRoute.Controls
