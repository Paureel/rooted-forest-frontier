import State

/-! Project-specific finite-color tree DP. The table has one candidate per
available root color at an internal node, never a list of vertex assignments.
Only the coloring objective is proved here; ForestState graph transport is
a distinct consuming obligation. -/
namespace AllGoodDP
open RMAF

inductive Paint where
  | leaf : Nat → Nat → Paint
  | node : Nat → Paint → Paint → Paint
  deriving DecidableEq, Repr

def root : Paint → Nat
  | .leaf _ c => c
  | .node c _ _ => c

def erase : Paint → Tree
  | .leaf x _ => .leaf x
  | .node _ l r => .node (erase l) (erase r)

def delta (a b : Nat) : Nat := if a == b then 0 else 1
def changes : Paint → Nat
  | .leaf _ _ => 0
  | .node c l r => changes l + delta c (root l) + changes r + delta c (root r)
def edgeCost (c : Nat) (p : Paint) := changes p + delta c (root p)

inductive Valid (cs : List Nat) (owner : Nat → Nat) : Tree → Paint → Prop where
  | leaf (x : Nat) (hc : owner x ∈ cs) : Valid cs owner (.leaf x) (.leaf x (owner x))
  | node {t u : Tree} {p q : Paint} (c : Nat) (hc : c ∈ cs)
      (hp : Valid cs owner t p) (hq : Valid cs owner u q) :
      Valid cs owner (.node t u) (.node c p q)

theorem valid_erase {cs owner t p} (h : Valid cs owner t p) : erase p = t := by
  induction h with
  | leaf => rfl
  | node c hc hp hq ihp ihq => simp [erase,ihp,ihq]

theorem best_exists {α : Type} (cost : α → Nat) (xs : List α) (hne : xs ≠ []) :
    ∃ p, best cost (fun _ => true) xs = some p := by
  cases hb : best cost (fun _ => true) xs with
  | some p => exact ⟨p,rfl⟩
  | none =>
    have hn := (best_none_iff cost (fun _ => true) xs).1 hb
    cases xs with
    | nil => exact False.elim (hne rfl)
    | cons a as => have := hn a (by simp); contradiction

def choose (cost : Paint → Nat) (xs : List Paint) : Paint :=
  (best cost (fun _ => true) xs).getD (.leaf 0 0)

theorem choose_spec (cost : Paint → Nat) (xs : List Paint) (hne : xs ≠ []) :
    choose cost xs ∈ xs ∧ ∀ p ∈ xs, cost (choose cost xs) ≤ cost p := by
  obtain ⟨p,hp⟩ := best_exists cost xs hne
  have hs := best_spec cost (fun _ => true) xs p hp
  simp only [choose,hp,Option.getD_some]
  exact ⟨hs.1,fun q hq => hs.2.2 q hq rfl⟩

def table (cs : List Nat) (owner : Nat → Nat) : Tree → List Paint
  | .leaf x => [.leaf x (owner x)]
  | .node l r =>
    let ls := table cs owner l
    let rs := table cs owner r
    cs.map fun c => .node c (choose (edgeCost c) ls) (choose (edgeCost c) rs)

theorem table_spec (cs : List Nat) (owner : Nat → Nat) (t : Tree)
    (hcs : cs ≠ []) (ho : ∀ x ∈ leaves t, owner x ∈ cs) :
    table cs owner t ≠ [] ∧
    (∀ p ∈ table cs owner t, Valid cs owner t p) ∧
    (∀ p, Valid cs owner t p → ∃ b ∈ table cs owner t,
      root b = root p ∧ changes b ≤ changes p) := by
  induction t with
  | leaf x =>
    refine ⟨by simp [table],?_,?_⟩
    · intro p hp
      have he : p = .leaf x (owner x) := by simpa [table] using hp
      subst p
      exact Valid.leaf x (ho x (by simp [leaves]))
    · intro p hp
      cases hp
      exact ⟨.leaf x (owner x),by simp [table],rfl,Nat.le_refl _⟩
  | node l r ihl ihr =>
    have hl := ihl (fun x hx => ho x (by simp [leaves,hx]))
    have hr := ihr (fun x hx => ho x (by simp [leaves,hx]))
    have pickl := fun c => choose_spec (edgeCost c) (table cs owner l) hl.1
    have pickr := fun c => choose_spec (edgeCost c) (table cs owner r) hr.1
    refine ⟨?_,?_,?_⟩
    · simpa [table] using hcs
    · intro p hp
      obtain ⟨c,hc,rfl⟩ := List.mem_map.1 hp
      exact Valid.node c hc (hl.2.1 _ (pickl c).1) (hr.2.1 _ (pickr c).1)
    · intro p hp
      cases hp with
      | node c hc hp hq =>
        obtain ⟨bl,hbl,hrootl,hcostl⟩ := hl.2.2 _ hp
        obtain ⟨br,hbr,hrootr,hcostr⟩ := hr.2.2 _ hq
        refine ⟨.node c (choose (edgeCost c) (table cs owner l))
          (choose (edgeCost c) (table cs owner r)),?_,rfl,?_⟩
        · exact List.mem_map.2 ⟨c,hc,rfl⟩
        · have hpl := (pickl c).2 bl hbl
          have hpr := (pickr c).2 br hbr
          simp only [edgeCost,hrootl,hrootr] at hpl hpr
          simp only [changes]
          omega

def solve (cs : List Nat) (owner : Nat → Nat) (t : Tree) : Paint :=
  choose changes (table cs owner t)

theorem solve_spec (cs : List Nat) (owner : Nat → Nat) (t : Tree)
    (hcs : cs ≠ []) (ho : ∀ x ∈ leaves t, owner x ∈ cs) :
    Valid cs owner t (solve cs owner t) ∧
    ∀ p, Valid cs owner t p → changes (solve cs owner t) ≤ changes p := by
  have ht := table_spec cs owner t hcs ho
  have hs := choose_spec changes (table cs owner t) ht.1
  refine ⟨ht.2.1 _ hs.1,?_⟩
  intro p hp
  obtain ⟨b,hb,_,hcost⟩ := ht.2.2 p hp
  exact Nat.le_trans (hs.2 b hb) hcost

theorem table_length (cs : List Nat) (owner : Nat → Nat) (t : Tree) :
    (table cs owner t).length = match t with | .leaf _ => 1 | .node _ _ => cs.length := by
  cases t <;> simp [table]

def vertices : Tree → Nat
  | .leaf _ => 1
  | .node l r => vertices l + vertices r + 1

-- Exact table visits in this coarse source model: one leaf row, and for
-- each internal root color two finite table scans plus one constructor.
def rowBound (r : Nat) (t : Tree) : Nat := match t with | .leaf _ => 1 | .node _ _ => r
def visits (r : Nat) : Tree → Nat
  | .leaf _ => 1
  | .node l s => visits r l + visits r s + r * (rowBound r l + rowBound r s + 1)

theorem row_bound (r : Nat) (t : Tree) : rowBound r t ≤ r + 1 := by
  cases t <;> simp [rowBound]

theorem visits_bound (r : Nat) (t : Tree) :
    visits r t ≤ vertices t * (r * (2 * (r + 1) + 1) + 1) := by
  induction t with
  | leaf x => simp [visits,vertices]
  | node l s hl hs =>
    have hb : r * (rowBound r l + rowBound r s + 1) ≤ r * (2 * (r + 1) + 1) :=
      Nat.mul_le_mul_left r (by have := row_bound r l; have := row_bound r s; omega)
    simp only [visits,vertices]
    rw [Nat.add_mul,Nat.add_mul]
    omega

end AllGoodDP
