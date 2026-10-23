import Std

/- One-shot recurrence route. No scientific-result imports, custom axioms,
   sorry, or native_decide. All algorithm-facing premises are explicit. -/
namespace RuntimeRepairRecurrence

structure Credit where
  p : Fin 4
  q : Fin 4
  valid : q.val ≤ p.val

def weight64 (p q : Nat) : Int :=
  match p, q with
  | 0, 0 => 64
  | 1, 0 => 32 | 1, 1 => 48
  | 2, 0 => 16 | 2, 1 => 24 | 2, 2 => 36
  | 3, 0 => 8 | 3, 1 => 12 | 3, 2 => 18 | 3, 3 => 27
  | _, _ => 0

def offset (p : Nat) : Int := (p : Int) - 3

-- A row's coefficient is scaled by 64*16. Costs are capped at four only
-- after separately disposing of negative-budget terminal children.
structure Child where
  cost : Nat
  p : Nat
  q : Nat
  deriving DecidableEq

def mass16 (cs : List Child) : Int :=
  (cs.map fun c => weight64 c.p c.q * (2 : Int) ^ (4-c.cost)).sum

def intercept (cs : List Child) : Int :=
  1 + (cs.map fun c => offset c.p).sum

def good (p q : Nat) (cs : List Child) : Prop :=
  mass16 cs ≤ 16 * weight64 p q ∧ intercept cs ≤ offset p

instance (p q : Nat) (cs : List Child) : Decidable (good p q cs) := inferInstanceAs
  (Decidable (mass16 cs ≤ 16 * weight64 p q ∧ intercept cs ≤ offset p))

-- The entire genuine 0<=q<=p<=3 domain is represented.
theorem domain_weights_positive :
    ∀ p ∈ [0,1,2,3], ∀ q ∈ [0,1,2,3], q ≤ p → 0 < weight64 p q := by decide

theorem finite_weight_formula :
    ∀ p ∈ [0,1,2,3], ∀ q ∈ [0,1,2,3], q ≤ p →
      weight64 p q * (2 : Int)^(p+q) = 64 * (3 : Int)^q := by decide

-- With alpha=128, the smallest continuation budget -4 has allowance
-- weight64/8 + p-3. The scaled inequality avoids any rational coercion.
theorem negative_boundary :
    ∀ p ∈ [0,1,2,3], ∀ q ∈ [0,1,2,3], q ≤ p →
      8 ≤ weight64 p q + 8 * offset p := by decide

-- The enumerated lifted branching/discharge schemas from G1--G3.
-- Source coverage of these rows is a separate, unproved obligation.
def liftedRows : List (Nat × Nat × List Child) :=
  (List.range 3).flatMap fun r =>
    (List.range (r+1)).flatMap fun t =>
      [(r,t,[⟨1,r,t⟩,⟨2,r,t⟩,⟨1,r+1,t⟩]),
       (r,t,[⟨1,r,t⟩,⟨3,r,t⟩,⟨1,r+1,t+1⟩])]

def dischargeRows : List (Nat × Nat × List Child) :=
  (List.range 2).flatMap fun r =>
    (List.range (r+1)).flatMap fun t =>
      [(r+1,t,[⟨1,r,t⟩]), (r+1,t+1,[⟨1,r,t⟩]),
       (r+2,t,[⟨2,r,t⟩]), (r+2,t+1,[⟨2,r,t⟩]),
       (r+1,t+1,[⟨1,r,t⟩,⟨2,r,t⟩]),
       (r+1,t,[⟨1,r+1,t⟩,⟨2,r,t⟩]),
       (r+1,t,[⟨1,r+1,t+1⟩,⟨3,r,t⟩])]

theorem lifted_rows_sound :
    ∀ row ∈ liftedRows, good row.1 row.2.1 row.2.2 := by decide

theorem discharge_rows_sound :
    ∀ row ∈ dischargeRows, good row.1 row.2.1 row.2.2 := by decide

theorem G4_at_least_four_hard :
    good 1 0 [⟨1,1,0⟩,⟨4,0,0⟩,⟨1,2,1⟩] := by decide

theorem G4_at_least_four_soft :
    good 1 1 [⟨1,1,1⟩,⟨4,0,0⟩,⟨1,2,2⟩] := by decide

-- Certified failures of count-only closure. These are arithmetic
-- obstructions, explicitly not source-reachable runtime counterexamples.
theorem G4_three_hard_fails :
    ¬ good 1 0 [⟨1,1,0⟩,⟨3,0,0⟩,⟨1,2,1⟩] := by decide

theorem G4_three_soft_fails :
    ¬ good 1 1 [⟨1,1,1⟩,⟨3,0,0⟩,⟨1,2,2⟩] := by decide

theorem literal_additive_two_soft_gap :
    (3 : Int) * 16 + 3 * 8 > 4 * 16 := by decide

-- An arbitrary row satisfying both exact coefficient and intercept
-- tests composes for every nonnegative scale X.
theorem affine_row_composition (X childMass parentMass childOffset parentOffset total : Int)
    (hX : 0 ≤ X) (hmass : childMass ≤ parentMass)
    (hoffset : childOffset ≤ parentOffset)
    (hcount : total ≤ X*childMass+childOffset) :
    total ≤ X*parentMass+parentOffset := by
  have hm := Int.mul_le_mul_of_nonneg_left hmass hX
  omega

theorem affine_boundary_sufficiency (gap residual scale : Int)
    (hg : 0 ≤ gap) (hb : residual ≤ 64*gap) (hs : 64 ≤ scale) :
    residual ≤ scale*gap := by
  have hm := Int.mul_le_mul_of_nonneg_right hs hg
  omega

-- Prefix-composition engine: V counts every expanded invocation, including
-- dead terminals; frontier roots themselves are excluded from V.
def PairBounds : List Int → List Int → Prop
  | [], [] => True
  | a::xs, b::ys => a ≤ b ∧ PairBounds xs ys
  | _, _ => False

theorem sum_le_of_forall2 {xs ys : List Int}
    (h : PairBounds xs ys) : xs.sum ≤ ys.sum := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp
    | cons b ys => simp [PairBounds] at h
  | cons a xs ih =>
    cases ys with
    | nil => simp [PairBounds] at h
    | cons b ys =>
      have hab : a ≤ b := h.1
      have ht : xs.sum ≤ ys.sum := ih h.2
      simp only [List.sum_cons]
      omega

theorem frontier_composition
    (total expanded : Int) (actual allowances : List Int)
    (count_identity : total = expanded + actual.sum)
    (boundary_bounds : PairBounds actual allowances) :
    total ≤ expanded + allowances.sum := by
  have h := sum_le_of_forall2 boundary_bounds
  omega

-- Unary internal normalization (trivial common merge/root removal)
-- does not create an invocation and is represented by equality.
theorem normalization_preserves_bound (before after cap : Int)
    (same_invocation : before = after) (h : after ≤ cap) : before ≤ cap := by omega

-- X denotes alpha*2^K, represented in units where all printed bounds are
-- integral after multiplying counts by 16. This is available for alpha=128
-- and K>=0. A/B hypotheses are separate, smaller-budget exit allowances.
-- C is allowed an additive +2, which is weaker than the originally proposed -1.
theorem joint_hard_from_weak_C (X A B C : Int)
    (hA : 16*A ≤ 4*X-32)
    (hB : 16*B ≤ 2*X-48)
    (hC : 16*C ≤ 2*X+32) :
    16*(1+A+B+C) ≤ 8*X-32 := by omega

theorem weak_C_exact_interface (X A B C : Int)
    (hA : 16*A = 4*X-32) (hB : 16*B = 2*X-48) :
    (16*(1+A+B+C) ≤ 8*X-32) ↔ (16*C ≤ 2*X+32) := by omega

theorem joint_hard_from_sufficient_C (X A B C : Int)
    (hA : 16*A ≤ 4*X-32)
    (hB : 16*B ≤ 2*X-48)
    (hC : 16*C ≤ 2*X-16) :
    16*(1+A+B+C) ≤ 8*X-80 := by omega

-- Soft incoming credit has its own exact exception interface.
theorem joint_soft_from_weak_C (X A B C : Int)
    (hA : 16*A ≤ 6*X-32)
    (hB : 16*B ≤ 2*X-48)
    (hC : 16*C ≤ 4*X+32) :
    16*(1+A+B+C) ≤ 12*X-32 := by omega

-- A finite prefix certificate bounds C by its expanded calls plus exit caps.
-- Passing this exact aggregate test implies the weak C allowance above.
theorem C_from_frontier (X C expanded : Int) (actual allowances : List Int)
    (count_identity : C = expanded + actual.sum)
    (boundary_bounds : PairBounds actual allowances)
    (frontier_test : 16*(expanded + allowances.sum) ≤ 2*X+32) :
    16*C ≤ 2*X+32 := by
  have h := frontier_composition C expanded actual allowances count_identity boundary_bounds
  omega

-- Includes the complete exact use-site composition, with all assumptions
-- visible and no imported geometric lemma.
theorem joint_hard_from_frontier (X A B C expanded : Int)
    (actual allowances : List Int)
    (hA : 16*A ≤ 4*X-32)
    (hB : 16*B ≤ 2*X-48)
    (count_identity : C = expanded + actual.sum)
    (boundary_bounds : PairBounds actual allowances)
    (frontier_test : 16*(expanded + allowances.sum) ≤ 2*X+32) :
    16*(1+A+B+C) ≤ 8*X-32 := by
  exact joint_hard_from_weak_C X A B C hA hB
    (C_from_frontier X C expanded actual allowances count_identity boundary_bounds frontier_test)

-- Further explicit debt-discharge templates. The structural mapping to
-- these schemas is deliberately a hypothesis, not a claimed theorem.
theorem hard_C_via_hard_exit (X C D : Int)
    (hc : C=1+D) (hd : 16*D ≤ 2*X-32) : 16*C ≤ 2*X+32 := by omega

theorem hard_C_via_two_generic_exits (X C D E : Int)
    (hc : C=1+D+E) (hd : 16*D ≤ X-48) (he : 16*E ≤ X-48) :
    16*C ≤ 2*X+32 := by omega

theorem dead_C (X : Int) (hX : 0 ≤ X) : 16 ≤ 2*X+32 := by omega

-- A cost-two single discharge certifies the C interface; cost-one generic
-- discharge does not, witnessed at X=128. Every invocation offset is present.
theorem cost_two_discharge (X C D : Int)
    (hc : C=1+D) (hd : 16*D ≤ 2*X-48) : 16*C ≤ 2*X+32 := by omega

theorem cost_one_mutation_fails :
    let X : Int := 128
    let D : Int := 29
    16*D = 4*X-48 ∧ ¬ (16*(1+D) ≤ 2*X+32) := by decide

#print axioms affine_row_composition
#print axioms joint_hard_from_frontier
#print axioms lifted_rows_sound
#print axioms discharge_rows_sound
#print axioms negative_boundary
end RuntimeRepairRecurrence
