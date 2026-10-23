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

end TripleDP.CostRoute.IndexRoute
