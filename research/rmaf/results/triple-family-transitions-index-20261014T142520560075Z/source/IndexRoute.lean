import FamilyAssembly

/-! One-shot independent finite-index supporting proof for family merge.
Only the old FamilyAssembly semantics are shared. No geometry constructor is
asserted. -/
namespace TripleDP.CostRoute.IndexRoute

variable {I J : Type}

/-- Enumerate the actual surviving indices; the proof field forbids the removed
member from even inhabiting the retained type. -/
def survivors [DecidableEq I] (o : I) : List I → List {x : I // x ≠ o}
  | [] => []
  | x :: xs => if h : x = o then survivors o xs else ⟨x, h⟩ :: survivors o xs

/-- Left/right constructors keep even equal-looking child names distinct. -/
inductive Joined (o : I) (p : J) where
  | boundary : Joined o p
  | left : {x : I // x ≠ o} → Joined o p
  | right : {y : J // y ≠ p} → Joined o p
  deriving DecidableEq

def enumeration [DecidableEq I] [DecidableEq J]
    (xs : List I) (ys : List J) (o : I) (p : J) : List (Joined o p) :=
  .boundary :: ((survivors o xs).map Joined.left ++ (survivors p ys).map Joined.right)

def closedEnumeration [DecidableEq I] [DecidableEq J]
    (xs : List I) (ys : List J) (o : I) (p : J) : List (Joined o p) :=
  (survivors o xs).map Joined.left ++ (survivors p ys).map Joined.right

def singletonEnums := enumeration ([0] : List Nat) ([0] : List Nat) 0 0

def singletonClosed := closedEnumeration ([0] : List Nat) ([0] : List Nat) 0 0

def collisionLeft : Joined (0 : Nat) (0 : Nat) := .left ⟨1, by decide⟩
def collisionRight : Joined (0 : Nat) (0 : Nat) := .right ⟨1, by decide⟩

example : singletonEnums.length = 1 := by decide
example : singletonClosed.length = 0 := by decide
example : collisionLeft ≠ collisionRight := by decide

theorem mem_survivors [DecidableEq I] (o : I) (xs : List I)
    (x : {x : I // x ≠ o}) : x ∈ survivors o xs ↔ x.val ∈ xs := by
  induction xs with
  | nil => simp [survivors]
  | cons a xs ih =>
    by_cases h : a = o
    · subst a
      simp [survivors, ih, x.property]
    · simp [survivors, h, ih, Subtype.ext_iff]

theorem survivors_nodup [DecidableEq I] (o : I) (xs : List I)
    (h : xs.Nodup) : (survivors o xs).Nodup := by
  induction xs with
  | nil => simp [survivors]
  | cons a xs ih =>
    have hd := List.nodup_cons.mp h
    by_cases ha : a = o
    · simp [survivors, ha, ih hd.2]
    · rw [survivors, dite_eq_right ha, List.nodup_cons]
      exact ⟨fun hx => hd.1 ((mem_survivors o xs ⟨a, ha⟩).mp hx), ih hd.2⟩

theorem survivors_length_absent [DecidableEq I] (o : I) (xs : List I)
    (h : o ∉ xs) : (survivors o xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha : a ≠ o := fun he => h (by simp [he])
    have ht : o ∉ xs := fun hm => h (List.mem_cons_of_mem a hm)
    simp [survivors, ha, ih ht]

theorem survivors_delete_one [DecidableEq I] (o : I) (xs : List I)
    (hd : xs.Nodup) (hm : o ∈ xs) :
    (survivors o xs).length + 1 = xs.length := by
  induction xs with
  | nil => simp at hm
  | cons a xs ih =>
    have hn := List.nodup_cons.mp hd
    by_cases ha : a = o
    · subst a
      simpa [survivors] using survivors_length_absent o xs hn.1
    · have ht : o ∈ xs := by
        rcases List.mem_cons.mp hm with he | ht
        · exact False.elim (ha he.symm)
        · exact ht
      have hh := ih hn.2 ht
      simp only [survivors, dite_eq_right ha, List.length_cons]
      omega

theorem survivors_forget [DecidableEq I] (o : I) (xs : List I) :
    (survivors o xs).map Subtype.val = xs.filter (fun x => decide (x ≠ o)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = o <;> simp [survivors, h, ih]

private theorem map_nodup {A B : Type} (f : A → B)
    (hf : ∀ x y, f x = f y → x = y) {xs : List A} (h : xs.Nodup) :
    (xs.map f).Nodup :=
  List.Pairwise.map f (fun x y hxy hEq => hxy (hf x y hEq)) h

theorem closedEnumeration_nodup [DecidableEq I] [DecidableEq J]
    (a : FiniteIndex I) (b : FiniteIndex J) (o : I) (p : J) :
    (closedEnumeration a.elems b.elems o p).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨map_nodup Joined.left (fun _ _ h => Joined.left.inj h)
      (survivors_nodup o a.elems a.nodup),
    map_nodup Joined.right (fun _ _ h => Joined.right.inj h)
      (survivors_nodup p b.elems b.nodup), ?_⟩
  intro x hx y hy he
  rcases List.mem_map.mp hx with ⟨x, _, rfl⟩
  rcases List.mem_map.mp hy with ⟨y, _, rfl⟩
  cases he

theorem boundary_not_closed [DecidableEq I] [DecidableEq J]
    (xs : List I) (ys : List J) (o : I) (p : J) :
    Joined.boundary ∉ closedEnumeration xs ys o p := by
  simp [closedEnumeration]

theorem enumeration_nodup [DecidableEq I] [DecidableEq J]
    (a : FiniteIndex I) (b : FiniteIndex J) (o : I) (p : J) :
    (enumeration a.elems b.elems o p).Nodup := by
  exact List.nodup_cons.mpr ⟨boundary_not_closed _ _ _ _, closedEnumeration_nodup a b o p⟩

theorem enumeration_complete [DecidableEq I] [DecidableEq J]
    (a : FiniteIndex I) (b : FiniteIndex J) (o : I) (p : J) (z : Joined o p) :
    z ∈ enumeration a.elems b.elems o p := by
  cases z with
  | boundary => simp [enumeration]
  | left x => simp [enumeration, mem_survivors, a.complete x.val]
  | right y => simp [enumeration, mem_survivors, b.complete y.val]

/-- Actual duplicate-free complete output enumeration. -/
def mergedFinite [DecidableEq I] [DecidableEq J]
    (a : FiniteIndex I) (b : FiniteIndex J) (o : I) (p : J) : FiniteIndex (Joined o p) where
  elems := enumeration a.elems b.elems o p
  nodup := enumeration_nodup a b o p
  complete := enumeration_complete a b o p

theorem left_injective (o : I) (p : J) (x y : {x : I // x ≠ o}) :
    (Joined.left x : Joined o p) = Joined.left y ↔ x = y := by
  constructor
  · exact Joined.left.inj
  · exact congrArg Joined.left

theorem right_injective (o : I) (p : J) (x y : {y : J // y ≠ p}) :
    (Joined.right x : Joined o p) = Joined.right y ↔ x = y := by
  constructor
  · exact Joined.right.inj
  · exact congrArg Joined.right

theorem left_right_separate (o : I) (p : J)
    (x : {x : I // x ≠ o}) (y : {y : J // y ≠ p}) :
    (Joined.left x : Joined o p) ≠ Joined.right y := by
  intro h
  cases h

theorem left_retained_iff [DecidableEq I] [DecidableEq J]
    (xs : List I) (ys : List J) (o : I) (p : J) (x : {x : I // x ≠ o}) :
    Joined.left x ∈ enumeration xs ys o p ↔ x.val ∈ xs := by
  simp [enumeration, mem_survivors]

theorem right_retained_iff [DecidableEq I] [DecidableEq J]
    (xs : List I) (ys : List J) (o : I) (p : J) (y : {y : J // y ≠ p}) :
    Joined.right y ∈ enumeration xs ys o p ↔ y.val ∈ ys := by
  simp [enumeration, mem_survivors]

theorem closed_complete_iff [DecidableEq I] [DecidableEq J]
    (a : FiniteIndex I) (b : FiniteIndex J) (o : I) (p : J) (z : Joined o p) :
    z ∈ closedEnumeration a.elems b.elems o p ↔ z ≠ Joined.boundary := by
  cases z with
  | boundary => simp [boundary_not_closed]
  | left x => simp [closedEnumeration, mem_survivors, a.complete x.val]
  | right y => simp [closedEnumeration, mem_survivors, b.complete y.val]

theorem enumeration_count [DecidableEq I] [DecidableEq J]
    (a : FiniteIndex I) (b : FiniteIndex J) (o : I) (p : J) :
    (mergedFinite a b o p).elems.length = a.elems.length + b.elems.length - 1 := by
  have hl := survivors_delete_one o a.elems a.nodup (a.complete o)
  have hr := survivors_delete_one p b.elems b.nodup (b.complete p)
  simp only [mergedFinite, enumeration, List.length_cons, List.length_append, List.length_map]
  omega

theorem closed_count [DecidableEq I] [DecidableEq J]
    (a : FiniteIndex I) (b : FiniteIndex J) (o : I) (p : J) :
    (closedEnumeration a.elems b.elems o p).length =
      (a.elems.length - 1) + (b.elems.length - 1) := by
  have hl := survivors_delete_one o a.elems a.nodup (a.complete o)
  have hr := survivors_delete_one p b.elems b.nodup (b.complete p)
  simp only [closedEnumeration, List.length_append, List.length_map]
  omega

/-- Child-index maps identify only the two designated members. -/
def fromLeft [DecidableEq I] (o : I) (p : J) (x : I) : Joined o p :=
  if h : x = o then .boundary else .left ⟨x, h⟩

def fromRight [DecidableEq J] (o : I) (p : J) (y : J) : Joined o p :=
  if h : y = p then .boundary else .right ⟨y, h⟩

theorem fromLeft_injective [DecidableEq I] (o : I) (p : J) (x y : I) :
    fromLeft o p x = fromLeft o p y ↔ x = y := by
  by_cases hx : x = o <;> by_cases hy : y = o
  · simp [hx, hy]
  · simp [fromLeft, hx, hy]
    exact Ne.symm hy
  · simp [fromLeft, hx, hy]
  · simp [fromLeft, hx, hy, Subtype.ext_iff]

theorem fromRight_injective [DecidableEq J] (o : I) (p : J) (x y : J) :
    fromRight o p x = fromRight o p y ↔ x = y := by
  by_cases hx : x = p <;> by_cases hy : y = p
  · simp [hx, hy]
  · simp [fromRight, hx, hy]
    exact Ne.symm hy
  · simp [fromRight, hx, hy]
  · simp [fromRight, hx, hy, Subtype.ext_iff]

theorem only_boundary_identified [DecidableEq I] [DecidableEq J]
    (o : I) (p : J) (x : I) (y : J) :
    fromLeft o p x = fromRight o p y ↔ x = o ∧ y = p := by
  by_cases hx : x = o <;> by_cases hy : y = p <;>
    simp [fromLeft, fromRight, hx, hy]

theorem all_joined_from_child [DecidableEq I] [DecidableEq J]
    (o : I) (p : J) (z : Joined o p) :
    (∃ x, fromLeft o p x = z) ∨ (∃ y, fromRight o p y = z) := by
  cases z with
  | boundary => exact Or.inl ⟨o, by simp [fromLeft]⟩
  | left x => exact Or.inl ⟨x.val, by simp [fromLeft, x.property]⟩
  | right y => exact Or.inr ⟨y.val, by simp [fromRight, y.property]⟩

theorem filter_boundary_eq_closed [DecidableEq I] [DecidableEq J]
    (xs : List I) (ys : List J) (o : I) (p : J) :
    (enumeration xs ys o p).filter (fun z => decide (z ≠ Joined.boundary)) =
      closedEnumeration xs ys o p := by
  simp [enumeration, closedEnumeration, List.filter_append, List.filter_map, Function.comp_def]

variable {α : Type} {l r : BTree α}

theorem survivors_are_family_closed [DecidableEq I]
    (L : Family l I) (o : I) (ho : L.boundary = some o) :
    (survivors o L.finite.elems).map Subtype.val = L.closedIndices := by
  rw [survivors_forget]
  simp [Family.closedIndices, ho]

theorem family_enumeration_count [DecidableEq I] [DecidableEq J]
    (L : Family l I) (R : Family r J) (o : I) (p : J) :
    (mergedFinite L.finite R.finite o p).elems.length = L.blockCount + R.blockCount - 1 :=
  enumeration_count L.finite R.finite o p

theorem family_closed_count [DecidableEq I] [DecidableEq J]
    (L : Family l I) (R : Family r J) (o : I) (p : J)
    (ho : L.boundary = some o) (hp : R.boundary = some p) :
    (closedEnumeration L.finite.elems R.finite.elems o p).length = L.cost + R.cost := by
  rw [closed_count]
  simp [Family.cost, Family.blockCount, boundaryCharge, ho, hp]

theorem boundary_charge_interpretation [DecidableEq I] [DecidableEq J]
    (xs : List I) (ys : List J) (o : I) (p : J) :
    (enumeration xs ys o p).length - boundaryCharge (some (Joined.boundary : Joined o p)) =
      (closedEnumeration xs ys o p).length := by
  simp [enumeration, closedEnumeration, boundaryCharge]

/-- This interface consumes a geometric family only after its finite indices and
boundary have been supplied. It assumes no count, cost, or closed-list equation. -/
theorem family_consumer_equations [DecidableEq I] [DecidableEq J]
    (L : Family l I) (R : Family r J) (o : I) (p : J)
    (ho : L.boundary = some o) (hp : R.boundary = some p)
    (G : Family (.node l r) (Joined o p))
    (hfinite : G.finite = mergedFinite L.finite R.finite o p)
    (hboundary : G.boundary = some Joined.boundary) :
    G.blockCount = L.blockCount + R.blockCount - 1 ∧
      G.closedIndices = closedEnumeration L.finite.elems R.finite.elems o p ∧
      G.cost = L.cost + R.cost := by
  have hcount : G.blockCount = L.blockCount + R.blockCount - 1 := by
    simp only [Family.blockCount, hfinite]
    exact enumeration_count L.finite R.finite o p
  have hclosed : G.closedIndices = closedEnumeration L.finite.elems R.finite.elems o p := by
    simp only [Family.closedIndices, hboundary, hfinite, mergedFinite]
    exact filter_boundary_eq_closed _ _ _ _
  refine ⟨hcount, hclosed, ?_⟩
  rw [cost_counts_closed_indices, hclosed]
  exact family_closed_count L R o p ho hp

#print axioms mergedFinite
#print axioms enumeration_count
#print axioms closed_count
#print axioms left_retained_iff
#print axioms right_retained_iff
#print axioms only_boundary_identified
#print axioms all_joined_from_child
#print axioms survivors_are_family_closed
#print axioms family_closed_count
#print axioms family_consumer_equations

end TripleDP.CostRoute.IndexRoute
