import FamilyAssembly

/-! Independent pointwise charge route. All sums run over original parent
indices. No geometric restriction theorem or filter inclusion-exclusion theorem
is imported. The child families in the consumer are conditional inputs. -/
namespace TripleDP.RestrictionCharge
open TripleDP.CostRoute

variable {I : Type}

def bit (b : Bool) : Nat := if b then 1 else 0

def weight : List I → (I → Bool) → Nat
  | [], _ => 0
  | i :: is, p => bit (p i) + weight is p

def closedCharge [DecidableEq I] (xs : List I) (live : I → Bool)
    (root : Option I) : Nat :=
  weight xs (fun i => live i && decide (root ≠ some i))

def duplicate (left right : I → Bool) : Option I → Nat
  | none => 0
  | some o => bit (left o && right o)

theorem weight_congr (xs : List I) (p q : I → Bool)
    (h : ∀ i ∈ xs, p i = q i) : weight xs p = weight xs q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [weight, h a (by simp), ih (fun i hi => h i (by simp [hi]))]

theorem weight_zero (xs : List I) (p : I → Bool)
    (h : ∀ i ∈ xs, p i = false) : weight xs p = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp [weight, bit, h a (by simp), ih (fun i hi => h i (by simp [hi]))]

theorem weight_true (xs : List I) : weight xs (fun _ => true) = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [weight, bit, ih, Nat.add_comm]

/-- Summing the local 0/1 balance, rather than comparing filtered cardinalities. -/
theorem covered_balance (xs : List I) (left right : I → Bool)
    (cover : ∀ i ∈ xs, left i = true ∨ right i = true) :
    weight xs left + weight xs right =
      xs.length + weight xs (fun i => left i && right i) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have hh := cover a (by simp)
    have ht := ih (fun i hi => cover i (by simp [hi]))
    cases hl : left a <;> cases hr : right a <;>
      simp [weight, bit, hl, hr] at hh ⊢ <;> omega

theorem weight_unique (xs : List I) (p : I → Bool) (o : I)
    (nodup : xs.Nodup) (mem : o ∈ xs)
    (only : ∀ i ∈ xs, p i = true → i = o) :
    weight xs p = bit (p o) := by
  induction xs with
  | nil => simp at mem
  | cons a xs ih =>
    have hn := List.nodup_cons.mp nodup
    by_cases ha : a = o
    · subst a
      have hz : weight xs p = 0 := weight_zero xs p (by
        intro i hi
        cases hp : p i with
        | false => rfl
        | true =>
          have he := only i (by simp [hi]) hp
          exact False.elim (hn.1 (he ▸ hi)))
      simp [weight, hz]
    · have hm : o ∈ xs := by simpa [List.mem_cons, eq_comm, ha] using mem
      have hp : p a = false := by
        cases he : p a with
        | false => rfl
        | true => exact False.elim (ha (only a (by simp) he))
      have ht := ih hn.2 hm (fun i hi => only i (by simp [hi]))
      simp [weight, hp, bit, ht]

/-- Exact count identity for a finite enumeration covered by two predicates,
whose intersection is confined to the optional distinguished index. -/
theorem count_balance (enum : FiniteIndex I) (left right : I → Bool)
    (root : Option I)
    (cover : ∀ i, left i = true ∨ right i = true)
    (overlap : ∀ i, left i = true → right i = true → root = some i) :
    weight enum.elems left + weight enum.elems right =
      enum.elems.length + duplicate left right root := by
  have hb := covered_balance enum.elems left right (fun i _ => cover i)
  have hd : weight enum.elems (fun i => left i && right i) =
      duplicate left right root := by
    cases hr : root with
    | none =>
      apply weight_zero
      intro i _
      cases hl : left i <;> cases hri : right i <;> simp [hl, hri]
      have hh := overlap i hl hri
      simp [hr] at hh
    | some o =>
      apply weight_unique enum.elems _ o enum.nodup (enum.complete o)
      intro i _ hi
      have hh := Bool.and_eq_true.mp hi
      have he := overlap i hh.1 hh.2
      rw [hr] at he
      exact (Option.some.inj he).symm
  omega

theorem split_charge [DecidableEq I] (xs : List I) (live : I → Bool)
    (root : Option I) :
    closedCharge xs live root +
      weight xs (fun i => live i && decide (root = some i)) = weight xs live := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    unfold closedCharge at *
    by_cases hr : root = some a <;> cases hl : live a <;>
      simp [weight, bit, hr, hl] at * <;> omega

theorem close_balance [DecidableEq I] (enum : FiniteIndex I) (live : I → Bool)
    (root : Option I) (rootLive : ∀ o, root = some o → live o = true) :
    closedCharge enum.elems live root + boundaryCharge root = weight enum.elems live := by
  have hs := split_charge enum.elems live root
  have hw : weight enum.elems (fun i => live i && decide (root = some i)) =
      boundaryCharge root := by
    cases hr : root with
    | none =>
      apply weight_zero
      intro i _
      simp [hr]
    | some o =>
      have h := weight_unique enum.elems (fun i => live i && decide (root = some i)) o
        enum.nodup (enum.complete o) (by
          intro i _ hi
          have he := of_decide_eq_true (Bool.and_eq_true.mp hi).2
          rw [hr] at he
          exact (Option.some.inj he).symm)
      simpa [hr, rootLive o hr, bit, boundaryCharge] using h
  omega

/-- The full charge budget, before choosing one of the four transition cases. -/
theorem charge_budget [DecidableEq I] (enum : FiniteIndex I)
    (left right : I → Bool) (parent leftRoot rightRoot : Option I)
    (cover : ∀ i, left i = true ∨ right i = true)
    (overlap : ∀ i, left i = true → right i = true → parent = some i)
    (leftRootLive : ∀ o, leftRoot = some o → left o = true)
    (rightRootLive : ∀ o, rightRoot = some o → right o = true) :
    closedCharge enum.elems left leftRoot + closedCharge enum.elems right rightRoot +
      boundaryCharge leftRoot + boundaryCharge rightRoot =
    closedCharge enum.elems (fun _ => true) parent + boundaryCharge parent +
      duplicate left right parent := by
  have hc := count_balance enum left right parent cover overlap
  have hl := close_balance enum left leftRoot leftRootLive
  have hr := close_balance enum right rightRoot rightRootLive
  have hp := close_balance enum (fun _ => true) parent (fun _ _ => rfl)
  have ht := weight_true enum.elems
  omega

/-- All four exact equations with child-root hypotheses shown at each use.
The option root may belong to a parent-closed index. -/
theorem four_charges [DecidableEq I] (enum : FiniteIndex I)
    (left right : I → Bool) (parent leftRoot rightRoot : Option I)
    (cover : ∀ i, left i = true ∨ right i = true)
    (overlap : ∀ i, left i = true → right i = true → parent = some i)
    (leftRootLive : ∀ o, leftRoot = some o → left o = true)
    (rightRootLive : ∀ o, rightRoot = some o → right o = true) :
    (parent = none →
      closedCharge enum.elems (fun _ => true) parent =
        closedCharge enum.elems left leftRoot + closedCharge enum.elems right rightRoot +
        boundaryCharge leftRoot + boundaryCharge rightRoot) ∧
    (∀ o, parent = some o → left o = true → right o = false → leftRoot = some o →
      closedCharge enum.elems (fun _ => true) parent =
        closedCharge enum.elems left leftRoot + closedCharge enum.elems right rightRoot +
        boundaryCharge rightRoot) ∧
    (∀ o, parent = some o → left o = false → right o = true → rightRoot = some o →
      closedCharge enum.elems (fun _ => true) parent =
        closedCharge enum.elems left leftRoot + closedCharge enum.elems right rightRoot +
        boundaryCharge leftRoot) ∧
    (∀ o, parent = some o → left o = true → right o = true →
      leftRoot = some o → rightRoot = some o →
      closedCharge enum.elems (fun _ => true) parent =
        closedCharge enum.elems left leftRoot + closedCharge enum.elems right rightRoot) := by
  have h := charge_budget enum left right parent leftRoot rightRoot cover overlap
    leftRootLive rightRootLive
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hp
    simp [hp, boundaryCharge, duplicate] at h
    omega
  · intro o hp hl hr hlo
    simp [hp, hl, hr, hlo, boundaryCharge, duplicate, bit] at h
    omega
  · intro o hp hl hr hro
    simp [hp, hl, hr, hro, boundaryCharge, duplicate, bit] at h
    omega
  · intro o hp hl hr hlo hro
    simp [hp, hl, hr, hlo, hro, boundaryCharge, duplicate, bit] at h
    omega

end TripleDP.RestrictionCharge
