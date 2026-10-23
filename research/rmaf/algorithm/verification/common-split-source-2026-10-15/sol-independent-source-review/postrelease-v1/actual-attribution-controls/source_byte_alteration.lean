import Std

/-! Executable ordinary rooted-MAF model and a finite-search correctness core.
No faster branching algorithm is asserted. See FORMAL.md for semantic scope. -/

namespace RMAF

inductive Tree where
  | leaf : Nat → Tree
  | node : Tree → Tree → Tree
  deriving DecidableEq, Repr

def leaves : Tree → List Nat
  | .leaf x => [x]
  | .node l r => leaves l ++ leaves r

/-- Binary shape is built into Tree; these hypotheses make labelling bijective
and ensure that the input trees have the identical canonical taxon set. -/
structure Instance where
  n : Nat
  left : Tree
  right : Tree
  labels_left : (leaves left).Perm (List.range n)
  labels_right : (leaves right).Perm (List.range n)

/-- Inductive rooted label-preserving isomorphism, independent of the Boolean
checker. No orientation of siblings is part of a phylogenetic tree. -/
inductive RootedIso : Tree → Tree → Prop where
  | leaf (x : Nat) : RootedIso (.leaf x) (.leaf x)
  | straight {a b c d : Tree} : RootedIso a c → RootedIso b d →
      RootedIso (.node a b) (.node c d)
  | swapped {a b c d : Tree} : RootedIso a d → RootedIso b c →
      RootedIso (.node a b) (.node c d)

/-- A labelled rooted isomorphism may swap the children at any vertex. -/
def sameShape : Tree → Tree → Bool
  | .leaf a, .leaf b => a == b
  | .node a b, .node c d =>
      (sameShape a c && sameShape b d) ||
      (sameShape a d && sameShape b c)
  | _, _ => false

theorem sameShape_refl (t : Tree) : sameShape t t = true := by
  induction t with
  | leaf x => simp [sameShape]
  | node a b ha hb => simp [sameShape, ha, hb]

theorem sameShape_correct (t u : Tree) : sameShape t u = true ↔ RootedIso t u := by
  induction t generalizing u with
  | leaf x =>
      cases u with
      | leaf y =>
          constructor
          · intro h
            have heq : x = y := by simpa [sameShape] using h
            subst y
            exact RootedIso.leaf x
          · intro h
            cases h
            simp [sameShape]
      | node c d =>
          constructor
          · intro h; simp [sameShape] at h
          · intro h; cases h
  | node a b ha hb =>
      cases u with
      | leaf y =>
          constructor
          · intro h; simp [sameShape] at h
          · intro h; cases h
      | node c d =>
          simp only [sameShape, Bool.or_eq_true, Bool.and_eq_true, ha, hb]
          constructor
          · intro h
            rcases h with h | h
            · exact RootedIso.straight h.1 h.2
            · exact RootedIso.swapped h.1 h.2
          · intro h
            cases h with
            | straight hc hd => exact Or.inl ⟨hc, hd⟩
            | swapped hc hd => exact Or.inr ⟨hc, hd⟩

/-- Empty selections give none; unary vertices are suppressed. -/
def restrict (selected : List Nat) : Tree → Option Tree
  | .leaf x => if selected.contains x then some (.leaf x) else none
  | .node l r =>
      match restrict selected l, restrict selected r with
      | none, none => none
      | some a, none => some a
      | none, some b => some b
      | some a, some b => some (.node a b)

theorem restrict_of_contains (t : Tree) (selected : List Nat)
    (h : ∀ x ∈ leaves t, selected.contains x = true) :
    restrict selected t = some t := by
  induction t with
  | leaf x =>
      rw [restrict, h x (by simp [leaves])]
      rfl
  | node l r hl hr =>
      have hleft : ∀ x ∈ leaves l, selected.contains x = true := by
        intro x hx
        exact h x (by simp [leaves, hx])
      have hright : ∀ x ∈ leaves r, selected.contains x = true := by
        intro x hx
        exact h x (by simp [leaves, hx])
      simp [restrict, hl hleft, hr hright]

abbrev Vertex := List Bool

def prependSide (side : Bool) (vs : List Vertex) : List Vertex :=
  vs.map (side :: ·)

/-- The rooted span includes paths from this root to every selected leaf.
Unary path vertices must be retained for embedding-disjointness checks. -/
def rootedSpan (selected : List Nat) : Tree → List Vertex
  | .leaf x => if selected.contains x then [[]] else []
  | .node l r =>
      let ls := rootedSpan selected l
      let rs := rootedSpan selected r
      if ls.isEmpty && rs.isEmpty then []
      else [] :: (prependSide false ls ++ prependSide true rs)

/-- The minimal embedding starts at the selected leaves' LCA, not the input root.
Once both children contribute, keep all intervening unary path vertices. -/
def minimalVertices (selected : List Nat) : Tree → List Vertex
  | .leaf x => if selected.contains x then [[]] else []
  | .node l r =>
      let ls := rootedSpan selected l
      let rs := rootedSpan selected r
      if ls.isEmpty then prependSide true (minimalVertices selected r)
      else if rs.isEmpty then prependSide false (minimalVertices selected l)
      else [] :: (prependSide false ls ++ prependSide true rs)

def disjointVertices (a b : List Vertex) : Bool :=
  a.all (fun v => !(b.contains v))

def pairwiseEmbeddings (t : Tree) : List (List Nat) → Bool
  | [] => true
  | b :: bs =>
      bs.all (fun c => disjointVertices (minimalVertices b t) (minimalVertices c t)) &&
      pairwiseEmbeddings t bs

def restrictionAgrees (t u : Tree) (b : List Nat) : Bool :=
  match restrict b t, restrict b u with
  | some s, some v => sameShape s v
  | _, _ => false

def partitionCheck (labels : List Nat) (bs : List (List Nat)) : Bool :=
  bs.all (fun b => !b.isEmpty) &&
  labels.all (fun x => bs.flatten.count x == 1) &&
  bs.flatten.all (fun x => labels.contains x)

def agreement (t u : Tree) (bs : List (List Nat)) : Bool :=
  partitionCheck (leaves t) bs && partitionCheck (leaves u) bs &&
  bs.all (restrictionAgrees t u) &&
  pairwiseEmbeddings t bs && pairwiseEmbeddings u bs

/-- Every assignment has one entry per leaf; tag equality defines its block.
Empty tags are discarded. Input labels here are 0, ..., n-1. -/
def blocks (a : List Nat) : List (List Nat) :=
  ((List.range a.length).map fun tag =>
      (List.range a.length).filter fun label => a[label]? == some tag).filter
    (fun b => !b.isEmpty)

def assignments (length tags : Nat) : List (List Nat) :=
  match length with
  | 0 => [[]]
  | n + 1 => (List.range tags).flatMap fun tag =>
      (assignments n tags).map (tag :: ·)

theorem assignments_complete (n tags : Nat) (a : List Nat)
    (hlen : a.length = n) (hbound : ∀ x ∈ a, x < tags) :
    a ∈ assignments n tags := by
  induction n generalizing a with
  | zero =>
      cases a with
      | nil => simp [assignments]
      | cons x xs => simp at hlen
  | succ n ih =>
      cases a with
      | nil => simp at hlen
      | cons x xs =>
          have hx : x < tags := hbound x (by simp)
          have hxs : ∀ y ∈ xs, y < tags := by
            intro y hy
            exact hbound y (by simp [hy])
          have hm : xs ∈ assignments n tags := ih xs (by simpa using hlen) hxs
          simp only [assignments, List.mem_flatMap]
          exact ⟨x, List.mem_range.mpr hx, List.mem_map.mpr ⟨xs, hm, rfl⟩⟩

theorem assignments_sound (n tags : Nat) (a : List Nat)
    (h : a ∈ assignments n tags) : a.length = n ∧ ∀ x ∈ a, x < tags := by
  induction n generalizing a with
  | zero =>
      have ha : a = [] := by simpa [assignments] using h
      subst a
      simp
  | succ n ih =>
      rcases List.mem_flatMap.mp h with ⟨tag, htag, ha⟩
      rcases List.mem_map.mp ha with ⟨xs, hxs, heq⟩
      subst a
      have hs := ih xs hxs
      refine ⟨by simp [hs.1], ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with heq | hmem
      · subst x; exact List.mem_range.mp htag
      · exact hs.2 x hmem

/-- Exhaustive search over a supplied candidate list. -/
def best {α : Type} (cost : α → Nat) (valid : α → Bool) : List α → Option α
  | [] => none
  | a :: as =>
      if valid a then
        match best cost valid as with
        | none => some a
        | some b => if cost a ≤ cost b then some a else some b
      else best cost valid as

theorem best_none_iff {α : Type} (cost : α → Nat) (valid : α → Bool)
    (xs : List α) : best cost valid xs = none ↔ ∀ a ∈ xs, valid a = false := by
  induction xs with
  | nil => simp [best]
  | cons a as ih =>
      cases hv : valid a <;> simp [best, hv, ih]
      cases htail : best cost valid as <;> simp
      split <;> simp

theorem best_spec {α : Type} (cost : α → Nat) (valid : α → Bool)
    (xs : List α) (b : α) (h : best cost valid xs = some b) :
    b ∈ xs ∧ valid b = true ∧ ∀ a ∈ xs, valid a = true → cost b ≤ cost a := by
  induction xs generalizing b with
  | nil => simp [best] at h
  | cons a as ih =>
      cases hv : valid a with
      | false =>
          have hb := ih b (by simpa [best, hv] using h)
          refine ⟨by simp [hb.1], hb.2.1, ?_⟩
          intro c hc hvc
          rcases List.mem_cons.mp hc with heq | hmem
          · subst c
            simp [hv] at hvc
          · exact hb.2.2 c hmem hvc
      | true =>
          cases ht : best cost valid as with
          | none =>
              have heq : a = b := Option.some.inj (by simpa [best, hv, ht] using h)
              subst b
              refine ⟨by simp, hv, ?_⟩
              intro c hc hvc
              rcases List.mem_cons.mp hc with heq | hmem
              · subst c; exact Nat.le_refl _
              · have hfalse := (best_none_iff cost valid as).mp ht c hmem
                simp [hfalse] at hvc
          | some v =>
              have hs := ih v ht
              by_cases hle : cost a ≤ cost v
              · have heq : a = b := Option.some.inj (by simpa [best, hv, ht, hle] using h)
                subst b
                refine ⟨by simp, hv, ?_⟩
                intro c hc hvc
                rcases List.mem_cons.mp hc with heq | hmem
                · subst c; exact Nat.le_refl _
                · exact Nat.le_trans hle (hs.2.2 c hmem hvc)
              · have heq : v = b := Option.some.inj (by simpa [best, hv, ht, hle] using h)
                subst b
                refine ⟨by simp [hs.1], hs.2.1, ?_⟩
                intro c hc hvc
                rcases List.mem_cons.mp hc with heq | hmem
                · subst c; omega
                · exact hs.2.2 c hmem hvc

theorem best_exists {α : Type} (cost : α → Nat) (valid : α → Bool)
    (xs : List α) (a : α) (hmem : a ∈ xs) (hvalid : valid a = true) :
    ∃ b, best cost valid xs = some b := by
  cases hs : best cost valid xs with
  | none =>
      have hf := (best_none_iff cost valid xs).mp hs a hmem
      simp [hf] at hvalid
  | some b => exact ⟨b, rfl⟩

def solve (n : Nat) (t u : Tree) : Option (List Nat) :=
  best (fun a => (blocks a).length) (fun a => agreement t u (blocks a))
    (assignments n n)

/-- Unconditional optimality over the executable assignment/embedding model.
The equivalence of that model to the graph-theoretic paper definition remains
a separate semantic interface obligation, explicitly recorded in FORMAL.md. -/
theorem assignment_solver_optimal (n : Nat) (t u : Tree) (winner : List Nat)
    (h : solve n t u = some winner) :
    agreement t u (blocks winner) = true ∧
    ∀ a : List Nat, a.length = n → (∀ x ∈ a, x < n) →
      agreement t u (blocks a) = true → (blocks winner).length ≤ (blocks a).length := by
  have hs := best_spec (fun a => (blocks a).length)
    (fun a => agreement t u (blocks a)) (assignments n n) winner h
  refine ⟨hs.2.1, ?_⟩
  intro a hlen hbound hagree
  exact hs.2.2 a (assignments_complete n n a hlen hbound) hagree

theorem assignment_solver_winner_valid (n : Nat) (t u : Tree) (winner : List Nat)
    (h : solve n t u = some winner) : winner.length = n ∧ ∀ x ∈ winner, x < n := by
  have hs := best_spec (fun a => (blocks a).length)
    (fun a => agreement t u (blocks a)) (assignments n n) winner h
  exact assignments_sound n n winner hs.1

namespace Controls

def leftTree : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def rightTree : Tree := .node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.leaf 3)

theorem proper_labels_left : leaves leftTree = [0, 1, 2, 3] := by decide
theorem proper_labels_right : leaves rightTree = [0, 1, 2, 3] := by decide

def exampleInstance : Instance := {
  n := 4, left := leftTree, right := rightTree,
  labels_left := by decide, labels_right := by decide
}

theorem different_full_trees : sameShape leftTree rightTree = false := by decide

theorem two_component_witness : agreement leftTree rightTree [[0, 1, 3], [2]] = true := by decide

/-- This planted forest has compatible two-leaf restrictions but intersecting
minimal embeddings. A topology-only checker would incorrectly accept it. -/
theorem overlap_rejected : agreement leftTree leftTree [[0, 2], [1, 3]] = false := by decide

theorem singleton_control : agreement leftTree rightTree [[0], [1], [2], [3]] = true := by decide

set_option maxRecDepth 10000 in
theorem minimum_is_two : (solve 4 leftTree rightTree).map (fun a => (blocks a).length) = some 2 := by decide

def isolatedEndpoint (a : List Nat) : Bool :=
  (blocks a).contains [0] || (blocks a).contains [1]

/-- Exhaustive (4^4 assignments) kernel check: every feasible forest in this
finite instance with endpoint 0 or 1 isolated has at least three components. -/
theorem endpoint_branch_costs_three :
    ((assignments 4 4).filter fun a =>
      agreement leftTree rightTree (blocks a) && isolatedEndpoint a).all
      (fun a => 3 ≤ (blocks a).length) = true := by decide

theorem every_agreement_at_least_two (a : List Nat) (hlen : a.length = 4)
    (hbound : ∀ x ∈ a, x < 4) (hagree : agreement leftTree rightTree (blocks a) = true) :
    2 ≤ (blocks a).length := by
  cases hs : solve 4 leftTree rightTree with
  | none => have hc := minimum_is_two; simp [hs] at hc
  | some winner =>
      have hc : (blocks winner).length = 2 := by simpa [hs] using minimum_is_two
      have hm := (assignment_solver_optimal 4 leftTree rightTree winner hs).2 a hlen hbound hagree
      omega

theorem every_isolated_endpoint_at_least_three (a : List Nat) (hlen : a.length = 4)
    (hbound : ∀ x ∈ a, x < 4) (hagree : agreement leftTree rightTree (blocks a) = true)
    (hisolated : isolatedEndpoint a = true) : 3 ≤ (blocks a).length := by
  have hm : a ∈ (assignments 4 4).filter (fun a =>
      agreement leftTree rightTree (blocks a) && isolatedEndpoint a) := by
    apply List.mem_filter.mpr
    exact ⟨assignments_complete 4 4 a hlen hbound, by simp [hagree, hisolated]⟩
  have hb := List.all_eq_true.mp endpoint_branch_costs_three a hm
  simpa using hb

/-- A concrete surviving optimum keeps both conflicting-cherry endpoints.
An endpoint-only isolation rule misses it and every equally good solution. -/
theorem endpoint_only_rule_refuted :
    agreement leftTree rightTree (blocks [0, 0, 1, 0]) = true ∧
    (blocks [0, 0, 1, 0]).length = 2 ∧
    isolatedEndpoint [0, 0, 1, 0] = false := by decide

end Controls

#print axioms sameShape_refl
#print axioms sameShape_correct
#print axioms restrict_of_contains
#print axioms assignments_complete
#print axioms assignments_sound
#print axioms best_none_iff
#print axioms best_spec
#print axioms best_exists
#print axioms assignment_solver_optimal
#print axioms assignment_solver_winner_valid
#print axioms Controls.proper_labels_left
#print axioms Controls.proper_labels_right
#print axioms Controls.different_full_trees
#print axioms Controls.two_component_witness
#print axioms Controls.overlap_rejected
#print axioms Controls.singleton_control
#print axioms Controls.minimum_is_two
#print axioms Controls.endpoint_branch_costs_three
#print axioms Controls.every_agreement_at_least_two
#print axioms Controls.every_isolated_endpoint_at_least_three
#print axioms Controls.endpoint_only_rule_refuted

end RMAF

CORRUPT
