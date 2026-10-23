import Std

/-! Source-independent full binary decision traces. A leaf means the final
forced unit cut. All numbers are integers at common denominator 233^(q+1).
This module does not assert that a source-core run has this grammar. -/
namespace ScaffoldProfiles

inductive Class where
  | one | two | three | many
  deriving DecidableEq, Repr

/-- Capped number of raw leaves. No deduplication occurs. -/
def join : Class → Class → Class
  | .one, .one => .two
  | .one, .two | .two, .one => .three
  | _, _ => .many

/-- A full binary prefix tree with depth at most q. Padding is only in
its common-denominator representation; every raw leaf has one final cut. -/
inductive Trace : Nat → Type where
  | leaf (q : Nat) : Trace q
  | fork {q : Nat} : Trace q → Trace q → Trace (q + 1)

def cls : Trace q → Class
  | .leaf _ => .one
  | .fork a b => join (cls a) (cls b)

def rawLeaves : Trace q → Nat
  | .leaf _ => 1
  | .fork a b => rawLeaves a + rawLeaves b

def weight : Trace q → Nat
  | .leaf q => 233 ^ q
  | .fork a b => 100 * (weight a + weight b)

/-- Bound on prefix mass, scaled by 233^3; actual raw mass has a further
factor 100/233 for the mandatory final unit cut. -/
def bound : Class → Nat
  | .one => 233^3
  | .two => 200 * 233^2
  | .three => 100 * 233^2 + 20000 * 233
  | .many => 100 * 233^2 + 10000 * 233 + 2000000

theorem join_bound (a b : Class) :
    100 * (bound a + bound b) ≤ 233 * bound (join a b) := by
  cases a <;> cases b <;> decide

theorem weight_bound (t : Trace q) :
    233^3 * weight t ≤ bound (cls t) * 233^q := by
  induction t with
  | leaf q => simp [weight, cls, bound]
  | @fork q a b ia ib =>
    have hs : 233^3 * weight a + 233^3 * weight b ≤
        (bound (cls a) + bound (cls b)) * 233^q := by
      simpa [Nat.add_mul] using Nat.add_le_add ia ib
    calc
      233^3 * weight (.fork a b) =
          100 * (233^3 * weight a + 233^3 * weight b) := by
            simp [weight, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 100 * ((bound (cls a) + bound (cls b)) * 233^q) :=
        Nat.mul_le_mul_left 100 hs
      _ = (100 * (bound (cls a) + bound (cls b))) * 233^q := by
        simp [Nat.mul_assoc]
      _ ≤ (233 * bound (join (cls a) (cls b))) * 233^q :=
        Nat.mul_le_mul_right (233^q) (join_bound (cls a) (cls b))
      _ = bound (cls (.fork a b)) * 233^(q+1) := by
        simp [cls, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem class_spec (t : Trace q) :
    (cls t = .one ↔ rawLeaves t = 1) ∧
    (cls t = .two ↔ rawLeaves t = 2) ∧
    (cls t = .three ↔ rawLeaves t = 3) ∧
    (cls t = .many ↔ 4 ≤ rawLeaves t) := by
  induction t with
  | leaf q => simp [cls, rawLeaves]
  | fork a b ia ib =>
    cases ha : cls a <;> cases hb : cls b <;>
      simp_all [cls, rawLeaves, join] <;> omega

/-- Every >=4-emission full trace has raw mass at most [2,3,4,4].
Cross-multiplication represents sum c^(-d) <= 975890000/233^4. -/
theorem at_least_four_extremum (t : Trace q) (h : 4 ≤ rawLeaves t) :
    233^3 * weight t ≤ 9758900 * 233^q := by
  have hc := (class_spec t).2.2.2.mpr h
  simpa [hc, bound] using weight_bound t

/-- The upper envelope for any full binary trace is the singleton raw [1]. -/
theorem bound_le_singleton (a : Class) : bound a ≤ 233^3 := by
  cases a <;> decide

theorem all_trace_singleton_bound (t : Trace q) : weight t ≤ 233^q := by
  have h := weight_bound t
  have hb := Nat.mul_le_mul_right (233^q) (bound_le_singleton (cls t))
  have hz : 0 < 233^3 := by decide
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans h hb) hz

/-- If neither two-parent core has raw [1], the old two-unit-plus-two-paid
wrapper is already safe. This finite class calculation is independent of
source coverage, original-cut costs, and target continuations. -/
theorem non_singletons_safe (a b : Class) (ha : a ≠ .one) (hb : b ≠ .one) :
    2*100*233^5 + 100^3*(bound a + bound b) < 233^6 := by
  cases a <;> cases b <;> simp_all [bound] <;> decide

/-- If one core has >=4 raw emissions, its worst possible other parent is [1]. -/
theorem four_plus_any_safe (a : Class) :
    2*100*233^5 + 100^3*(bound .many + bound a) < 233^6 := by
  cases a <;> decide

/-- Literal expected full vector [1,1,3,4,5,6,6] after scaling by 233^6. -/
theorem pin_numerator :
    2*100*233^5 + 100^3*233^3 + 100^4*233^2 + 100^5*233 + 2*100^6 =
    159752208278600 := by decide

theorem pin_denominator : 233^6 = 160005726539569 := by decide

theorem pin_strict : 159752208278600 < 160005726539569 := by decide

#print axioms join_bound
#print axioms weight_bound
#print axioms class_spec
#print axioms at_least_four_extremum
#print axioms bound_le_singleton
#print axioms all_trace_singleton_bound
#print axioms non_singletons_safe
#print axioms four_plus_any_safe
#print axioms pin_numerator
#print axioms pin_denominator
#print axioms pin_strict
end ScaffoldProfiles

namespace ScaffoldProfiles
/-- The deepest emission is the least profitable place for the extra unit. -/
theorem progress_one_one :
    2*100*233^3 + 100^3*233 + 100^4 < 233^4 := by decide

theorem progress_one_two :
    2*100*233^4 + 100^3*233^2 + 100^4*233 + 100^5 < 233^5 := by decide

theorem progress_one_three :
    2*100*233^5 + 100^3*233^3 + 100^4*233^2 + 100^5*233 + 100^6 < 233^6 := by decide

theorem raw_one_one_fails : 233^3 < 2*100*233^2 + 2*100^3 := by decide

theorem raw_one_two_fails : 233^4 < 2*100*233^3 + 100^3*233 + 2*100^4 := by decide

theorem raw_one_three_fails :
    233^5 < 2*100*233^4 + 100^3*233^2 + 100^4*233 + 2*100^5 := by decide

#print axioms progress_one_one
#print axioms progress_one_two
#print axioms progress_one_three
#print axioms raw_one_one_fails
#print axioms raw_one_two_fails
#print axioms raw_one_three_fails
end ScaffoldProfiles
