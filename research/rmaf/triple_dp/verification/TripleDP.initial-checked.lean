import Std

/-! Kernel-checked pieces of the triple terminal algorithm.
The min-plus DP theorem is universal over explicitly supplied transition rules.
The LCA lemmas concern actual binary-tree addresses. The correspondence from
graph agreement forests to these automaton rules is NOT asserted here. -/

namespace TripleDP

inductive BTree (α : Type) where
  | leaf : α → BTree α
  | node : BTree α → BTree α → BTree α
  deriving DecidableEq, Repr

structure Rule (σ : Type) where
  left : σ
  right : σ
  toll : Nat

variable {α σ : Type} [DecidableEq σ]

inductive Derives (initial : α → List σ) (rules : σ → List (Rule σ)) :
    BTree α → σ → Nat → Prop where
  | leaf {x s} : s ∈ initial x → Derives initial rules (.leaf x) s 0
  | node {l r s q a b} : q ∈ rules s →
      Derives initial rules l q.left a → Derives initial rules r q.right b →
      Derives initial rules (.node l r) s (a + b + q.toll)

def candidate (l r : σ → Option Nat) (q : Rule σ) : Option Nat := do
  let a ← l q.left
  let b ← r q.right
  return a + b + q.toll

def table (initial : α → List σ) (rules : σ → List (Rule σ)) :
    BTree α → σ → Option Nat
  | .leaf x, s => if s ∈ initial x then some 0 else none
  | .node l r, s =>
      ((rules s).filterMap (candidate (table initial rules l)
        (table initial rules r))).min?

omit [DecidableEq σ] in
theorem candidate_some (l r : σ → Option Nat) (q : Rule σ) (c : Nat) :
    candidate l r q = some c ↔
      ∃ a b, l q.left = some a ∧ r q.right = some b ∧ c = a + b + q.toll := by
  cases hl : l q.left <;> cases hr : r q.right <;> simp [candidate, hl, hr]
  omega

/-- A compressed value is attained by a derivation, and is no greater than
the cost of any derivation. This is the optimal-substructure theorem needed
to replace every child-cost set by one minimum per boundary state. -/
theorem table_correct (initial : α → List σ) (rules : σ → List (Rule σ))
    (t : BTree α) :
    (∀ s c, table initial rules t s = some c → Derives initial rules t s c) ∧
    (∀ s c, Derives initial rules t s c →
      ∃ d, table initial rules t s = some d ∧ d ≤ c) := by
  induction t with
  | leaf x =>
      constructor
      · intro s c h
        by_cases hs : s ∈ initial x
        · have hc : c = 0 := by simpa [table, hs] using h.symm
          subst c
          exact Derives.leaf hs
        · simp [table, hs] at h
      · intro s c h
        cases h with
        | leaf hs => exact ⟨0, by simp [table, hs], Nat.le_refl 0⟩
  | node l r hl hr =>
      constructor
      · intro s c h
        have hm := List.min?_mem h
        rcases List.mem_filterMap.mp hm with ⟨q, hq, hc⟩
        rcases (candidate_some _ _ q c).mp hc with ⟨a, b, ha, hb, heq⟩
        subst c
        exact Derives.node hq (hl.1 _ _ ha) (hr.1 _ _ hb)
      · intro s c h
        cases h with
        | node hq ha hb =>
            rcases hl.2 _ _ ha with ⟨a', hat, hac⟩
            rcases hr.2 _ _ hb with ⟨b', hbt, hbc⟩
            rename_i q a b
            let xs := (rules s).filterMap
              (candidate (table initial rules l) (table initial rules r))
            have hm : a' + b' + q.toll ∈ xs := by
              apply List.mem_filterMap.mpr
              exact ⟨q, hq, (candidate_some _ _ q _).mpr ⟨a', b', hat, hbt, rfl⟩⟩
            cases ht : xs.min? with
            | none =>
                have hempty : xs = [] := List.min?_eq_none_iff.mp ht
                simp [hempty] at hm
            | some d =>
                refine ⟨d, ht, ?_⟩
                have hd := (List.min?_eq_some_iff.mp ht).2 _ hm
                omega

theorem table_optimal (initial : α → List σ) (rules : σ → List (Rule σ))
    (t : BTree α) (s : σ) (c : Nat) (h : table initial rules t s = some c) :
    Derives initial rules t s c ∧ ∀ d, Derives initial rules t s d → c ≤ d := by
  have hc := table_correct initial rules t
  refine ⟨hc.1 s c h, ?_⟩
  intro d hd
  rcases hc.2 s d hd with ⟨e, he, hed⟩
  have hce : c = e := Option.some.inj (h.symm.trans he)
  omega

theorem table_none_iff (initial : α → List σ) (rules : σ → List (Rule σ))
    (t : BTree α) (s : σ) :
    table initial rules t s = none ↔ ∀ c, ¬ Derives initial rules t s c := by
  constructor
  · intro h c hc
    rcases (table_correct initial rules t).2 s c hc with ⟨d, hd, _⟩
    simp [h] at hd
  · intro h
    cases ht : table initial rules t s with
    | none => rfl
    | some c => exact False.elim (h c ((table_correct initial rules t).1 s c ht))

/-- Closing two independent child configurations can be minimized separately.
This identity removes a quadratic Cartesian-product scan from the recurrence. -/
theorem minimum_pair_sum (xs ys : List Nat) (a b : Nat)
    (ha : xs.min? = some a) (hb : ys.min? = some b) :
    (xs.flatMap fun x => ys.map fun y => x + y).min? = some (a + b) := by
  apply List.min?_eq_some_iff.mpr
  have hxa := List.min?_eq_some_iff.mp ha
  have hyb := List.min?_eq_some_iff.mp hb
  constructor
  · apply List.mem_flatMap.mpr
    exact ⟨a, hxa.1, List.mem_map.mpr ⟨b, hyb.1, rfl⟩⟩
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨x, hx, hxy⟩
    rcases List.mem_map.mp hxy with ⟨y, hy, heq⟩
    have hax := hxa.2 x hx
    have hby := hyb.2 y hy
    omega

inductive Mask where
  | a | b | c | ab | ac | bc
  deriving DecidableEq, Repr

def Mask.value : Mask → Nat
  | .a => 1 | .b => 2 | .c => 4 | .ab => 3 | .ac => 5 | .bc => 6

def masks : List Mask := [.a, .b, .c, .ab, .ac, .bc]

def join : Mask → Mask → Option Mask
  | .a, .b | .b, .a => some .ab
  | .a, .c | .c, .a => some .ac
  | .b, .c | .c, .b => some .bc
  | _, _ => none

theorem join_exact (a b : Mask) :
    (∃ c, join a b = some c) ↔
    (a.value &&& b.value = 0 ∧ a.value ||| b.value < 7) := by
  cases a <;> cases b <;> simp [join, Mask.value]

theorem join_records_union (a b c : Mask) (h : join a b = some c) :
    c.value = a.value ||| b.value := by
  cases a <;> cases b <;> cases c <;> simp_all [join, Mask.value]

theorem proper_mask (a : Mask) : 0 < a.value ∧ a.value < 7 := by
  cases a <;> decide

theorem exactly_six_joins :
    (masks.flatMap fun a => masks.filterMap fun b => join a b).length = 6 := by decide

def boundaryStates : List (Option Mask) := none :: masks.map some

def charge : Option Mask → Nat
  | none => 0
  | some _ => 1

/-- Explicit transition relation for a single bad color. This unoptimized
enumeration is used only to check finite controls against the universal
automaton theorem; production factors the independent closing choices. -/
def badRules : Option Mask → List (Rule (Option Mask))
  | none => boundaryStates.flatMap fun l => boundaryStates.map fun r =>
      ⟨l, r, charge l + charge r⟩
  | some out =>
      (boundaryStates.map fun r => ⟨some out, r, charge r⟩) ++
      (boundaryStates.map fun l => ⟨l, some out, charge l⟩) ++
      (masks.flatMap fun a => masks.filterMap fun b =>
        if join a b = some out then some ⟨some a, some b, 0⟩ else none)

def tripleInitial : Nat → List (Option Mask)
  | 0 => [some .a] | 1 => [some .b] | 2 => [some .c] | _ => []

def tripleTree : BTree Nat := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)

def finish (t : BTree Nat) : Option Nat :=
  (boundaryStates.filterMap fun s =>
    (table tripleInitial badRules t s).map (fun c => c + charge s)).min?

theorem bad_triple_control : finish tripleTree = some 2 := by decide

theorem bad_triple_one_region_impossible : finish tripleTree ≠ some 1 := by
  rw [bad_triple_control]
  decide

abbrev Address := List Bool

def lca : Address → Address → Address
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => if a = b then a :: lca as bs else []

/-- This is a necessary property of connected vertex subsets of a rooted tree.
It is deliberately named LCA-closed, not asserted equivalent to connected. -/
def LCAClosed (region : Address → Prop) : Prop :=
  ∀ a b, region a → region b → region (lca a b)

theorem cross_children_use_root (region : Address → Prop) (h : LCAClosed region)
    (a b : Address) (ha : region (false :: a)) (hb : region (true :: b)) :
    region [] := by
  simpa [lca] using h (false :: a) (true :: b) ha hb

theorem root_absent_no_crossing (region : Address → Prop) (h : LCAClosed region)
    (hroot : ¬ region []) :
    ¬ ((∃ a, region (false :: a)) ∧ (∃ b, region (true :: b))) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact hroot (cross_children_use_root region h a b ha hb)

theorem child_restriction_closed (region : Address → Prop) (h : LCAClosed region)
    (side : Bool) : LCAClosed (fun a => region (side :: a)) := by
  intro a b ha hb
  simpa [lca] using h (side :: a) (side :: b) ha hb

theorem at_most_one_open (regions : Nat → Address → Prop)
    (disjoint : ∀ i j v, regions i v → regions j v → i = j)
    (i j : Nat) (hi : regions i []) (hj : regions j []) : i = j :=
  disjoint i j [] hi hj

def stateCount (good bad : Nat) := 1 + good + 6 * bad
def joinCount (good bad : Nat) := good + 6 * bad
def transitionCount (good bad : Nat) :=
  1 + 2 * (stateCount good bad - 1) + joinCount good bad

theorem exact_transition_count (good bad : Nat) :
    transitionCount good bad = 1 + 3 * good + 18 * bad := by
  simp [transitionCount, stateCount, joinCount]
  omega

theorem states_linear (good bad : Nat) : stateCount good bad ≤ 1 + 6 * (good + bad) := by
  simp [stateCount]
  omega

theorem transitions_linear (good bad : Nat) :
    transitionCount good bad ≤ 1 + 18 * (good + bad) := by
  rw [exact_transition_count]
  omega

theorem total_transition_bound (internal good bad : Nat) :
    internal * transitionCount good bad ≤ internal * (1 + 18 * (good + bad)) :=
  Nat.mul_le_mul_left internal (transitions_linear good bad)

#print axioms candidate_some
#print axioms table_correct
#print axioms table_optimal
#print axioms table_none_iff
#print axioms minimum_pair_sum
#print axioms join_exact
#print axioms join_records_union
#print axioms proper_mask
#print axioms exactly_six_joins
#print axioms bad_triple_control
#print axioms bad_triple_one_region_impossible
#print axioms cross_children_use_root
#print axioms root_absent_no_crossing
#print axioms child_restriction_closed
#print axioms at_most_one_open
#print axioms exact_transition_count
#print axioms states_linear
#print axioms transitions_linear
#print axioms total_transition_bound

end TripleDP
