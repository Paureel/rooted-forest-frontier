import Std

/- GLOBAL-Q constituent: actual graph edge deletion, not a graph/executable
   implementation of the pure-bridge or triple completion imports. -/
namespace GlobalQ

universe u
variable {V : Type u}

/-- Reachability after deleting a predicate of original edges. The adjacency
    relation may be made symmetric for an undirected source tree. -/
inductive Reach (adj cut : V → V → Prop) : V → V → Prop where
  | refl (v : V) : Reach adj cut v v
  | step {a b c : V} : adj a b → ¬ cut a b → Reach adj cut b c → Reach adj cut a c

/-- An original optimum region remains inside one precut region whenever
    every precut edge belongs to the original optimum cut set. -/
theorem cut_subset_reach {adj C K : V → V → Prop}
    (hCK : ∀ a b, C a b → K a b) {a b : V}
    (h : Reach adj K a b) : Reach adj C a b := by
  induction h with
  | refl v => exact Reach.refl v
  | @step a b c hab hK hbc ih =>
    exact Reach.step hab (fun hC => hK (hCK a b hC)) ih

/-- The partition refinement direction required by one-original-optimum
    survival, for the partitions represented by actual original edge cuts. -/
def PartitionRefines (fine coarse : V → V → Prop) : Prop :=
  ∀ a b, fine a b → coarse a b

theorem original_optimum_refines_precut {adj C K : V → V → Prop}
    (hCK : ∀ a b, C a b → K a b) :
    PartitionRefines (Reach adj K) (Reach adj C) := by
  intro a b h
  exact cut_subset_reach hCK h

/-- The unused optimum cut edges, as original-edge predicates. -/
def Residual (C K : V → V → Prop) (a b : V) : Prop := K a b ∧ ¬ C a b

/-- Precutted plus residual edges delete exactly the original optimum edges.
    No suppression, empty component, or artificial rho is used. -/
theorem residual_deletion_exact {C K : V → V → Prop}
    (hCK : ∀ a b, C a b → K a b) (a b : V) :
    (C a b ∨ Residual C K a b) ↔ K a b := by
  constructor
  · intro h
    cases h with
    | inl hC => exact hCK a b hC
    | inr hR => exact hR.1
  · intro hK
    by_cases hC : C a b
    · exact Or.inl hC
    · exact Or.inr ⟨hK, hC⟩

/-- Edge-deletion equality transports to actual graph paths in both directions. -/
theorem residual_reach_exact {adj C K : V → V → Prop}
    (hCK : ∀ a b, C a b → K a b) (a b : V) :
    Reach adj (fun x y => C x y ∨ Residual C K x y) a b ↔ Reach adj K a b := by
  constructor
  · intro h
    exact cut_subset_reach (fun x y hK => (residual_deletion_exact hCK x y).mpr hK) h
  · intro h
    exact cut_subset_reach (fun x y hUnion => (residual_deletion_exact hCK x y).mp hUnion) h

/-- A proposition-level corruption control: removing the cut-subset
    hypothesis would make original-optimum refinement false. -/
theorem refinement_without_cut_subset_is_false :
    ¬ (∀ (adj C K : Bool → Bool → Prop),
        PartitionRefines (Reach adj K) (Reach adj C)) := by
  intro h
  have hPath : Reach (fun a b : Bool => a ≠ b) (fun _ _ => False) false true :=
    Reach.step (by decide) (fun h => h) (Reach.refl true)
  have hBad := h (fun a b : Bool => a ≠ b) (fun _ _ => True) (fun _ _ => False) false true hPath
  have hEq : ∀ {a b : Bool}, Reach (fun a b : Bool => a ≠ b) (fun _ _ => True) a b → a = b := by
    intro a b hp
    cases hp with
    | refl v => rfl
    | step _ hCut _ => exact False.elim (hCut True.intro)
  have hf : (false : Bool) = true := hEq hBad
  cases hf

/-- A center component of a b-spoke quotient star retains b-r optimum
    boundary edges after r spoke cuts. Half-budget balancing forces half
    of the original spokes to be paid. This is a quotient weight statement,
    not a lower bound on actual local agreement distance. -/
theorem star_half_budget_requires_half (b r : Nat)
    (hr : r ≤ b) (hbalance : b - r ≤ b / 2) : b - b / 2 ≤ r := by
  omega

/-- The global residual count can be used for every local witness. -/
theorem half_residual_bounds_each (b r d : Nat)
    (hr : b - b / 2 ≤ r) (hd : d ≤ b - r) : d ≤ b / 2 := by
  omega

/-- Precut plus additional costs telescope to total cuts, only under the
    explicit nonredundant cut/component interface m=r+1. -/
theorem paid_component_accounting (r m p : Nat)
    (hm : m = r + 1) (hp : m ≤ p) : r + (p - m) = p - 1 := by
  omega

/-- Exact rational upper bound for sqrt(2), with no decimal evaluation. -/
theorem sqrt_upper_squared : (2 : Rat) < (142/100 : Rat)*(142/100 : Rat) := by
  decide +kernel

/-- Exact rational arithmetic needed by the prelicensed alternate. Its
    transfer from rational upper bounds to a real radical is a separate
    consumer step, not an assumed Lean Real implementation. -/
theorem alternate_upper_squared_certificate :
    (9/4 : Rat) * (1+142/100) < (23391/10000 : Rat) * (23391/10000 : Rat) := by
  decide +kernel

/-- A nonvacuous uniform rational lower-radical-approximation certificate.
    The inequality s*s <= 2 admits, for example, s=7/5. -/
theorem rational_subsqrt_certificate (s : Rat)
    (hs0 : 0 ≤ s) (hs2 : s*s ≤ 2) :
    (9/4 : Rat) * (1+s) < (23391/10000 : Rat) * (23391/10000 : Rat) := by
  have hsBound : s < (142/100 : Rat) := by
    apply Rat.not_le.mp
    intro hn
    have h1 : (142/100 : Rat) * (142/100 : Rat) ≤ s * (142/100 : Rat) :=
      Rat.mul_le_mul_of_nonneg_right hn (by decide +kernel)
    have h2 : s * (142/100 : Rat) ≤ s*s :=
      Rat.mul_le_mul_of_nonneg_left hn hs0
    have h3 := Rat.le_trans (Rat.le_trans h1 h2) hs2
    exact (by decide +kernel : ¬ ((142/100 : Rat)*(142/100 : Rat) ≤ 2)) h3
  have hsum : 1+s < (1+142/100 : Rat) := by grind
  have hprod := Rat.mul_lt_mul_of_pos_left hsum (by decide +kernel : (0 : Rat) < 9/4)
  have hfixed := alternate_upper_squared_certificate
  grind

example : (0 : Rat) ≤ 7/5 ∧ (7/5 : Rat)*(7/5 : Rat) ≤ 2 := by decide +kernel

#print axioms original_optimum_refines_precut
#print axioms residual_reach_exact
#print axioms refinement_without_cut_subset_is_false
#print axioms star_half_budget_requires_half
#print axioms half_residual_bounds_each
#print axioms paid_component_accounting
#print axioms sqrt_upper_squared
#print axioms alternate_upper_squared_certificate
#print axioms rational_subsqrt_certificate
end GlobalQ
