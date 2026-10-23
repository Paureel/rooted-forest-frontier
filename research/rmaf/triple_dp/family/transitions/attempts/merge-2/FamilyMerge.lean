import FiniteSelection

namespace TripleDP.Transitions
open TripleDP.CostRoute

variable {α I J : Type} {l r : BTree α}

abbrev MergeIndex (I : Type) (o : J) := Sum I {j : J // j ≠ o}

/-- Keep the left boundary index as the representative of the two open blocks. -/
def mergeSupport (f : Family l I) (g : Family r J) (o : I) (p : J) :
    MergeIndex I p → Address → Prop
  | .inl i, a => liftSupport false (f.support i) a ∨
      (i = o ∧ (a = [] ∨ liftSupport true (g.support p) a))
  | .inr j, a => liftSupport true (g.support j.val) a

@[simp] theorem mergeSupport_left_root (f : Family l I) (g : Family r J)
    (o i : I) (p : J) : mergeSupport f g o p (.inl i) [] ↔ i = o := by
  simp [mergeSupport, liftSupport]

@[simp] theorem mergeSupport_right_root (f : Family l I) (g : Family r J)
    (o : I) (p : J) (j : {j : J // j ≠ p}) :
    ¬ mergeSupport f g o p (.inr j) [] := by simp [mergeSupport, liftSupport]

@[simp] theorem mergeSupport_left_left (f : Family l I) (g : Family r J)
    (o i : I) (p : J) (a : Address) :
    mergeSupport f g o p (.inl i) (false :: a) ↔ f.support i a := by
  simp [mergeSupport, liftSupport]

@[simp] theorem mergeSupport_left_right (f : Family l I) (g : Family r J)
    (o i : I) (p : J) (a : Address) :
    mergeSupport f g o p (.inl i) (true :: a) ↔ i = o ∧ g.support p a := by
  simp [mergeSupport, liftSupport]

@[simp] theorem mergeSupport_right_left (f : Family l I) (g : Family r J)
    (o : I) (p : J) (j : {j : J // j ≠ p}) (a : Address) :
    ¬ mergeSupport f g o p (.inr j) (false :: a) := by
  simp [mergeSupport, liftSupport]

@[simp] theorem mergeSupport_right_right (f : Family l I) (g : Family r J)
    (o : I) (p : J) (j : {j : J // j ≠ p}) (a : Address) :
    mergeSupport f g o p (.inr j) (true :: a) ↔ g.support j.val a := by
  simp [mergeSupport, liftSupport]

def merge [DecidableEq J] (f : Family l I) (g : Family r J) (o : I) (p : J)
    (ho : f.boundary = some o) (hp : g.boundary = some p) :
    Family (.node l r) (MergeIndex I p) where
  finite := indexSum f.finite (selectIndex g.finite (fun j => j ≠ p))
  support := mergeSupport f g o p
  bounded := by
    intro i a hi
    cases i with
    | inl i =>
      rcases hi with hi | ⟨_, rfl | hi⟩
      · exact (closeBoth f g).bounded (.inl i) a hi
      · trivial
      · exact (closeBoth f g).bounded (.inr p) a hi
    | inr j => exact (closeBoth f g).bounded (.inr j.val) a hi
  convex := by
    intro i
    cases i with
    | inl i =>
      by_cases hi : i = o
      · subst i
        apply (rooted_region_decomposition (mergeSupport f g o p (.inl o)) (by simp)).mpr
        intro side
        cases side with
        | false =>
          constructor
          · simpa [PathConvex] using f.convex o
          · intro _; simpa using (f.root_spec o).mpr ho
        | true =>
          constructor
          · simpa [PathConvex] using g.convex p
          · intro _; simpa using (g.root_spec p).mpr hp
      · simpa [PathConvex, mergeSupport, hi] using liftSupport_convex false _ (f.convex i)
    | inr j => exact liftSupport_convex true _ (g.convex j.val)
  labelled := by
    intro i
    cases i with
    | inl i =>
      rcases f.labelled i with ⟨a, x, hx, hi⟩
      exact ⟨false :: a, x, hx, Or.inl ⟨rfl, hi⟩⟩
    | inr j =>
      rcases g.labelled j.val with ⟨a, x, hx, hj⟩
      exact ⟨true :: a, x, hx, rfl, hj⟩
  disjoint := by
    intro i j a hi hj
    cases a with
    | nil =>
      cases i with
      | inl i =>
        have hi' : i = o := by simpa using hi
        cases j with
        | inl j => have hj' : j = o := by simpa using hj
                   exact congrArg Sum.inl (hi'.trans hj'.symm)
        | inr j => simp at hj
      | inr i => simp at hi
    | cons side a =>
      cases side with
      | false =>
        cases i with
        | inl i =>
          have hi' : f.support i a := by simpa using hi
          cases j with
          | inl j =>
            have hj' : f.support j a := by simpa using hj
            exact congrArg Sum.inl (f.disjoint i j a hi' hj')
          | inr j => simp at hj
        | inr i => simp at hi
      | true =>
        cases i with
        | inl i =>
          have hi' : i = o ∧ g.support p a := by simpa using hi
          cases j with
          | inl j =>
            have hj' : j = o ∧ g.support p a := by simpa using hj
            exact congrArg Sum.inl (hi'.1.trans hj'.1.symm)
          | inr j =>
            have hj' : g.support j.val a := by simpa using hj
            exact False.elim (j.property (g.disjoint p j.val a hi'.2 hj').symm)
        | inr i =>
          have hi' : g.support i.val a := by simpa using hi
          cases j with
          | inl j =>
            have hj' : j = o ∧ g.support p a := by simpa using hj
            exact False.elim (i.property (g.disjoint i.val p a hi' hj'.2))
          | inr j =>
            have hj' : g.support j.val a := by simpa using hj
            exact congrArg Sum.inr (Subtype.ext (g.disjoint i.val j.val a hi' hj'))
  covers := by
    intro a x hx
    cases a with
    | nil => exact False.elim hx
    | cons side a =>
      cases side with
      | false =>
        rcases f.covers a x hx with ⟨i, hi⟩
        exact ⟨.inl i, Or.inl ⟨rfl, hi⟩⟩
      | true =>
        rcases g.covers a x hx with ⟨j, hj⟩
        by_cases h : j = p
        · subst j
          exact ⟨.inl o, Or.inr ⟨rfl, Or.inr ⟨rfl, hj⟩⟩⟩
        · exact ⟨.inr ⟨j, h⟩, rfl, hj⟩
  boundary := some (.inl o)
  root_spec := by
    intro i
    cases i <;> simp [eq_comm]

theorem merge_count [DecidableEq J] (f : Family l I) (g : Family r J)
    (o : I) (p : J) (ho : f.boundary = some o) (hp : g.boundary = some p) :
    (merge f g o p ho hp).blockCount = f.blockCount + g.blockCount - 1 := by
  have hr := selectIndex_nonboundary_length g p hp
  have hg := close_cost g
  rw [hp] at hg
  change g.cost + 1 = g.blockCount at hg
  change (indexSum f.finite (selectIndex g.finite (fun j => j ≠ p))).elems.length = _
  simp only [indexSum, List.length_append, List.length_map]
  change f.blockCount + (selectIndex g.finite (fun j => j ≠ p)).elems.length = _
  omega

theorem merge_cost [DecidableEq J] (f : Family l I) (g : Family r J)
    (o : I) (p : J) (ho : f.boundary = some o) (hp : g.boundary = some p) :
    (merge f g o p ho hp).cost = f.cost + g.cost := by
  have hn := merge_count f g o p ho hp
  have hf := close_cost f
  have hg := close_cost g
  have hm := close_cost (merge f g o p ho hp)
  rw [ho] at hf
  rw [hp] at hg
  change f.cost + 1 = f.blockCount at hf
  change g.cost + 1 = g.blockCount at hg
  change (merge f g o p ho hp).cost + 1 = (merge f g o p ho hp).blockCount at hm
  omega

#print axioms mergeSupport_left_root
#print axioms mergeSupport_right_root
#print axioms mergeSupport_left_left
#print axioms mergeSupport_left_right
#print axioms mergeSupport_right_left
#print axioms mergeSupport_right_right
#print axioms merge
#print axioms merge_count
#print axioms merge_cost
end TripleDP.Transitions
