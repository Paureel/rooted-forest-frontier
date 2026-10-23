import ConnectedRegions

/-! Problem-specific independent family assembly route. No trimming is assumed.
Indices are enumerated exactly once; supports carry actual tree vertices.
Labels are the labels of leaf vertices in BTree, including repeated values. -/
namespace TripleDP.CostRoute
open TripleDP

variable {α I J : Type}

def Vertex : BTree α → Address → Prop
  | .leaf _, a => a = []
  | .node _ _, [] => True
  | .node l _, false :: a => Vertex l a
  | .node _ r, true :: a => Vertex r a

def LeafAt : BTree α → Address → α → Prop
  | .leaf x, a, y => a = [] ∧ y = x
  | .node _ _, [], _ => False
  | .node l _, false :: a, x => LeafAt l a x
  | .node _ r, true :: a, x => LeafAt r a x

structure FiniteIndex (I : Type) where
  elems : List I
  nodup : elems.Nodup
  complete : ∀ i, i ∈ elems

private theorem nodup_map_injective {A B : Type} (f : A → B)
    (inj : ∀ a b, f a = f b → a = b) (xs : List A) (h : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have hh := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        rcases List.mem_map.mp hm with ⟨b, hb, he⟩
        exact hh.1 ((inj b a he) ▸ hb)
      · exact ih hh.2

def indexSum (a : FiniteIndex I) (b : FiniteIndex J) : FiniteIndex (Sum I J) where
  elems := a.elems.map Sum.inl ++ b.elems.map Sum.inr
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨nodup_map_injective _ (fun _ _ h => Sum.inl.inj h) _ a.nodup,
      nodup_map_injective _ (fun _ _ h => Sum.inr.inj h) _ b.nodup, ?_⟩
    intro x hx y hy he
    rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨j, _, rfl⟩
    cases he
  complete := by
    intro s
    cases s with
    | inl i => simp [a.complete i]
    | inr j => simp [b.complete j]

def boundaryCharge : Option I → Nat
  | none => 0
  | some _ => 1

/-- Every index denotes a distinct nonempty labelled region. The root belongs
exactly to the optional distinguished open region. Coverage and disjointness
therefore give every leaf vertex exactly one family index. -/
structure Family (t : BTree α) (I : Type) where
  finite : FiniteIndex I
  support : I → Address → Prop
  bounded : ∀ i a, support i a → Vertex t a
  convex : ∀ i, PathConvex (support i)
  labelled : ∀ i, ∃ a x, LeafAt t a x ∧ support i a
  disjoint : ∀ i j a, support i a → support j a → i = j
  covers : ∀ a x, LeafAt t a x → ∃ i, support i a
  boundary : Option I
  root_spec : ∀ i, support i [] ↔ boundary = some i

def Family.blockCount {t : BTree α} (f : Family t I) : Nat := f.finite.elems.length

def Family.cost {t : BTree α} (f : Family t I) : Nat :=
  f.blockCount - boundaryCharge f.boundary

theorem boundaryCharge_le_count {t : BTree α} (f : Family t I) :
    boundaryCharge f.boundary ≤ f.blockCount := by
  cases hb : f.boundary with
  | none => simp [boundaryCharge]
  | some i =>
      have hm := f.finite.complete i
      have hn : f.finite.elems ≠ [] := by intro h; simp [h] at hm
      have hp := List.length_pos_iff.mpr hn
      simp only [boundaryCharge, Family.blockCount]
      omega

theorem close_cost {t : BTree α} (f : Family t I) :
    f.cost + boundaryCharge f.boundary = f.blockCount := by
  have h := boundaryCharge_le_count f
  simp only [Family.cost]
  omega

/-- The charged blocks are exactly the enumerated indices other than the
root-containing index. This list witnesses the counting interpretation of cost. -/
def Family.closedIndices {t : BTree α} [DecidableEq I] (f : Family t I) : List I :=
  match f.boundary with
  | none => f.finite.elems
  | some o => f.finite.elems.filter (fun i => decide (i ≠ o))

private theorem filter_omit_one_length [DecidableEq I] (xs : List I)
    (hd : xs.Nodup) (o : I) (ho : o ∈ xs) :
    (xs.filter (fun i => decide (i ≠ o))).length + 1 = xs.length := by
  induction xs with
  | nil => simp at ho
  | cons a xs ih =>
    have hh := List.nodup_cons.mp hd
    by_cases ha : a = o
    · subst a
      have he : xs.filter (fun i => decide (i ≠ o)) = xs := by
        apply List.filter_eq_self.mpr
        intro i hi
        have hn : i ≠ o := by intro h; subst i; exact hh.1 hi
        simp [hn]
      rw [List.filter_cons, ite_eq_right (by simp), he]
      rfl
    · have hm : o ∈ xs := by
        rcases List.mem_cons.mp ho with he | hm
        · exact False.elim (ha he.symm)
        · exact hm
      have hn := ih hh.2 hm
      rw [List.filter_cons, ite_eq_left (by simp [ha]), List.length_cons, List.length_cons]
      omega

theorem cost_counts_closed_indices {t : BTree α} [DecidableEq I] (f : Family t I) :
    f.cost = f.closedIndices.length := by
  cases hb : f.boundary with
  | none => simp [Family.cost, Family.blockCount, Family.closedIndices, hb, boundaryCharge]
  | some o =>
    have h := filter_omit_one_length f.finite.elems f.finite.nodup o (f.finite.complete o)
    simp only [Family.cost, Family.blockCount, Family.closedIndices, hb, boundaryCharge]
    omega

theorem mem_closedIndices_iff {t : BTree α} [DecidableEq I] (f : Family t I) (i : I) :
    i ∈ f.closedIndices ↔ ¬ f.support i [] := by
  rw [f.root_spec i]
  cases hb : f.boundary with
  | none => simp [Family.closedIndices, hb, f.finite.complete i]
  | some o =>
    simp only [Family.closedIndices, hb, List.mem_filter, decide_eq_true_eq, Option.some.injEq]
    constructor
    · rintro ⟨_, h⟩ he
      exact h he.symm
    · intro h
      exact ⟨f.finite.complete i, fun he => h he.symm⟩

def liftSupport (side : Bool) (s : Address → Prop) : Address → Prop
  | [] => False
  | other :: a => other = side ∧ s a

theorem liftSupport_convex (side : Bool) (s : Address → Prop)
    (hs : PathConvex s) : PathConvex (liftSupport side s) := by
  intro a b ha hb v hv
  cases a with
  | nil => exact False.elim ha
  | cons a as =>
    rcases ha with ⟨heq, ha⟩
    subst a
    cases b with
    | nil => exact False.elim hb
    | cons b bs =>
      rcases hb with ⟨heq, hb⟩
      subst b
      cases v with
      | nil => simpa [OnPath, lca] using hv.1
      | cons c cs =>
        have hv' : side = c ∧ lca as bs <+: cs := by
          simpa [lca] using hv.1
        rcases hv' with ⟨rfl, hv'⟩
        refine ⟨rfl, hs as bs ha hb cs ⟨hv', ?_⟩⟩
        simpa using hv.2

def closedSupport {l r : BTree α} (f : Family l I) (g : Family r J) :
    Sum I J → Address → Prop
  | .inl i => liftSupport false (f.support i)
  | .inr j => liftSupport true (g.support j)

/-- Actual family constructor for the close-both transition. Child root
regions become closed in the parent; the parent root stays unused. -/
def closeBoth {l r : BTree α} (f : Family l I) (g : Family r J) :
    Family (.node l r) (Sum I J) where
  finite := indexSum f.finite g.finite
  support := closedSupport f g
  bounded := by
    intro i a h
    cases i <;> cases a with
    | nil => exact False.elim h
    | cons s as =>
      rcases h with ⟨rfl, h⟩
      first | exact f.bounded _ _ h | exact g.bounded _ _ h
  convex := by
    intro i
    cases i with
    | inl i => exact liftSupport_convex false _ (f.convex i)
    | inr j => exact liftSupport_convex true _ (g.convex j)
  labelled := by
    intro i
    cases i with
    | inl i =>
      rcases f.labelled i with ⟨a, x, hx, hi⟩
      exact ⟨false :: a, x, hx, rfl, hi⟩
    | inr j =>
      rcases g.labelled j with ⟨a, x, hx, hi⟩
      exact ⟨true :: a, x, hx, rfl, hi⟩
  disjoint := by
    intro i j a hi hj
    cases a with
    | nil => cases i <;> exact False.elim hi
    | cons s as =>
      cases i with
      | inl i =>
        rcases hi with ⟨rfl, hi⟩
        cases j with
        | inl j => exact congrArg Sum.inl (f.disjoint i j as hi hj.2)
        | inr j => cases hj.1
      | inr i =>
        rcases hi with ⟨rfl, hi⟩
        cases j with
        | inl j => cases hj.1
        | inr j => exact congrArg Sum.inr (g.disjoint i j as hi hj.2)
  covers := by
    intro a x hx
    cases a with
    | nil => exact False.elim hx
    | cons s as =>
      cases s with
      | false =>
        rcases f.covers as x hx with ⟨i, hi⟩
        exact ⟨Sum.inl i, rfl, hi⟩
      | true =>
        rcases g.covers as x hx with ⟨j, hj⟩
        exact ⟨Sum.inr j, rfl, hj⟩
  boundary := none
  root_spec := by intro i; cases i <;> simp [closedSupport, liftSupport]

theorem closeBoth_count {l r : BTree α} (f : Family l I) (g : Family r J) :
    (closeBoth f g).blockCount = f.blockCount + g.blockCount := by
  simp [Family.blockCount, closeBoth, indexSum]

/-- The toll is exactly the number of formerly open child blocks, on the
constructed family. This is the close-both case of the four DP transitions. -/
theorem closeBoth_cost {l r : BTree α} (f : Family l I) (g : Family r J) :
    (closeBoth f g).cost = f.cost + g.cost +
      boundaryCharge f.boundary + boundaryCharge g.boundary := by
  have hf := close_cost f
  have hg := close_cost g
  have hc := closeBoth_count f g
  change (closeBoth f g).blockCount - 0 = _
  omega

/-- Add the parent root to a child support rooted at the child root. -/
theorem withRoot_lift_convex (side : Bool) (s : Address → Prop)
    (hs : PathConvex s) (hr : s []) :
    PathConvex (fun a => a = [] ∨ liftSupport side s a) := by
  apply (rooted_pathConvex_iff_prefixClosed (fun a => a = [] ∨ liftSupport side s a) (Or.inl rfl)).mpr
  intro a ha p hp
  rcases ha with rfl | ha
  · exact Or.inl (List.prefix_nil.mp hp)
  · cases a with
    | nil => exact False.elim ha
    | cons b bs =>
      rcases ha with ⟨hbs, ha⟩
      cases p with
      | nil => exact Or.inl rfl
      | cons c cs =>
        rcases List.cons_prefix_cons.mp hp with ⟨hcb, hcs⟩
        exact Or.inr ⟨hcb.trans hbs,
          (rooted_pathConvex_iff_prefixClosed s hr).mp hs bs ha cs hcs⟩

def adjoinRootSupport {t : BTree α} (f : Family t I) (o i : I) (a : Address) : Prop :=
  (i = o ∧ a = []) ∨ f.support i a

/-- Universal family-level insertion of a root at one distinguished index.
The sole geometric premise is a single-region convexity statement; no family
preservation, enumeration, disjointness or cost fact is assumed. -/
def adjoinRoot {l r : BTree α} (f : Family (.node l r) I) (o : I)
    (hn : f.boundary = none)
    (hc : PathConvex (fun a => a = [] ∨ f.support o a)) :
    Family (.node l r) I where
  finite := f.finite
  support := adjoinRootSupport f o
  bounded := by
    intro i a ha
    rcases ha with ⟨_, rfl⟩ | ha
    · trivial
    · exact f.bounded i a ha
  convex := by
    intro i
    by_cases hi : i = o
    · subst i
      simpa [PathConvex, adjoinRootSupport] using hc
    · simpa [PathConvex, adjoinRootSupport, hi] using f.convex i
  labelled := by
    intro i
    rcases f.labelled i with ⟨a, x, hx, hi⟩
    exact ⟨a, x, hx, Or.inr hi⟩
  disjoint := by
    intro i j a hi hj
    rcases hi with ⟨rfl, rfl⟩ | hi
    · rcases hj with ⟨rfl, _⟩ | hj
      · rfl
      · have h := (f.root_spec j).mp hj
        simp [hn] at h
    · rcases hj with ⟨rfl, rfl⟩ | hj
      · have h := (f.root_spec i).mp hi
        simp [hn] at h
      · exact f.disjoint i j a hi hj
  covers := by
    intro a x hx
    rcases f.covers a x hx with ⟨i, hi⟩
    exact ⟨i, Or.inr hi⟩
  boundary := some o
  root_spec := by
    intro i
    have hnroot : ¬ f.support i [] := by
      intro h
      have h := (f.root_spec i).mp h
      simp [hn] at h
    simp [adjoinRootSupport, hnroot, eq_comm]

def extendLeft {l r : BTree α} (f : Family l I) (g : Family r J)
    (o : I) (ho : f.boundary = some o) : Family (.node l r) (Sum I J) :=
  adjoinRoot (closeBoth f g) (.inl o) rfl
    (withRoot_lift_convex false (f.support o) (f.convex o) ((f.root_spec o).mpr ho))

def extendRight {l r : BTree α} (f : Family l I) (g : Family r J)
    (o : J) (ho : g.boundary = some o) : Family (.node l r) (Sum I J) :=
  adjoinRoot (closeBoth f g) (.inr o) rfl
    (withRoot_lift_convex true (g.support o) (g.convex o) ((g.root_spec o).mpr ho))

theorem extendLeft_count {l r : BTree α} (f : Family l I) (g : Family r J)
    (o : I) (ho : f.boundary = some o) :
    (extendLeft f g o ho).blockCount = f.blockCount + g.blockCount :=
  closeBoth_count f g

theorem extendRight_count {l r : BTree α} (f : Family l I) (g : Family r J)
    (o : J) (ho : g.boundary = some o) :
    (extendRight f g o ho).blockCount = f.blockCount + g.blockCount :=
  closeBoth_count f g

theorem extendLeft_cost {l r : BTree α} (f : Family l I) (g : Family r J)
    (o : I) (ho : f.boundary = some o) :
    (extendLeft f g o ho).cost = f.cost + g.cost + boundaryCharge g.boundary := by
  have hf := close_cost f
  have hg := close_cost g
  have hc := extendLeft_count f g o ho
  have hb := close_cost (extendLeft f g o ho)
  rw [ho] at hf
  change f.cost + 1 = f.blockCount at hf
  change (extendLeft f g o ho).cost + 1 = (extendLeft f g o ho).blockCount at hb
  omega

theorem extendRight_cost {l r : BTree α} (f : Family l I) (g : Family r J)
    (o : J) (ho : g.boundary = some o) :
    (extendRight f g o ho).cost = f.cost + g.cost + boundaryCharge f.boundary := by
  have hf := close_cost f
  have hg := close_cost g
  have hc := extendRight_count f g o ho
  have hb := close_cost (extendRight f g o ho)
  rw [ho] at hg
  change g.cost + 1 = g.blockCount at hg
  change (extendRight f g o ho).cost + 1 = (extendRight f g o ho).blockCount at hb
  omega

def Family.hasLabel {t : BTree α} (f : Family t I) (i : I) (x : α) : Prop :=
  ∃ a, LeafAt t a x ∧ f.support i a

theorem closeBoth_hasLabel_left {l r : BTree α} (f : Family l I) (g : Family r J)
    (i : I) (x : α) :
    (closeBoth f g).hasLabel (.inl i) x ↔ f.hasLabel i x := by
  constructor
  · rintro ⟨a, hx, hi⟩
    cases a with
    | nil => exact False.elim hx
    | cons b bs =>
      rcases hi with ⟨rfl, hi⟩
      exact ⟨bs, hx, hi⟩
  · rintro ⟨a, hx, hi⟩
    exact ⟨false :: a, hx, rfl, hi⟩

theorem closeBoth_hasLabel_right {l r : BTree α} (f : Family l I) (g : Family r J)
    (i : J) (x : α) :
    (closeBoth f g).hasLabel (.inr i) x ↔ g.hasLabel i x := by
  constructor
  · rintro ⟨a, hx, hi⟩
    cases a with
    | nil => exact False.elim hx
    | cons b bs =>
      rcases hi with ⟨rfl, hi⟩
      exact ⟨bs, hx, hi⟩
  · rintro ⟨a, hx, hi⟩
    exact ⟨true :: a, hx, rfl, hi⟩

theorem adjoinRoot_hasLabel {l r : BTree α} (f : Family (.node l r) I)
    (o : I) (hn : f.boundary = none)
    (hc : PathConvex (fun a => a = [] ∨ f.support o a)) (i : I) (x : α) :
    (adjoinRoot f o hn hc).hasLabel i x ↔ f.hasLabel i x := by
  constructor
  · rintro ⟨a, hx, hi⟩
    rcases hi with ⟨_, rfl⟩ | hi
    · exact False.elim hx
    · exact ⟨a, hx, hi⟩
  · rintro ⟨a, hx, hi⟩
    exact ⟨a, hx, Or.inr hi⟩

#print axioms closeBoth_hasLabel_left
#print axioms closeBoth_hasLabel_right
#print axioms adjoinRoot_hasLabel
#print axioms cost_counts_closed_indices
#print axioms mem_closedIndices_iff
#print axioms withRoot_lift_convex
#print axioms adjoinRoot
#print axioms extendLeft
#print axioms extendRight
#print axioms extendLeft_count
#print axioms extendRight_count
#print axioms extendLeft_cost
#print axioms extendRight_cost
#print axioms liftSupport_convex
#print axioms closeBoth
#print axioms closeBoth_count
#print axioms closeBoth_cost
end TripleDP.CostRoute
