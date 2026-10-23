import Std

/-! Conditional consumer logic and exact integer arithmetic only.
No source-cut realization, terminal algorithm, or safe-cover generator is supplied.
-/
namespace BalancedSafeCover

def IsOptimum {P : Type} (valid : P → Prop) (cost : P → Nat) (p : P) : Prop :=
  valid p ∧ ∀ q, valid q → cost p ≤ cost q

/-- A supplied exact completion chooses a valid minimum within one refinement family.
All graph/executable obligations remain explicit in these hypotheses. -/
structure ExactCompletion {P F : Type} (valid : P → Prop) (cost : P → Nat)
    (refines : P → F → Prop) (witness : F → P) where
  valid : ∀ f, valid (witness f)
  refines : ∀ f, refines (witness f) f
  minimum : ∀ f p, valid p → refines p f → cost (witness f) ≤ cost p

theorem one_optimum_suffices {P F : Type} (valid : P → Prop) (cost : P → Nat)
    (refines : P → F → Prop) (witness : F → P) (cover : List F)
    (completion : ExactCompletion valid cost refines witness)
    (p : P) (hp : IsOptimum valid cost p)
    (hsurvive : ∃ f ∈ cover, refines p f) :
    (∃ f ∈ cover, cost (witness f) = cost p) ∧
      (∀ f ∈ cover, cost p ≤ cost (witness f)) := by
  rcases hsurvive with ⟨f, hf, hpf⟩
  have lower : ∀ g ∈ cover, cost p ≤ cost (witness g) := by
    intro g _
    exact hp.2 _ (completion.valid g)
  have upper := completion.minimum f p hp.1 hpf
  exact ⟨⟨f, hf, Nat.le_antisymm upper (lower f hf)⟩, lower⟩

theorem conditional_decision_exact {P F : Type} (valid : P → Prop)
    (cost : P → Nat) (refines : P → F → Prop) (witness : F → P)
    (cover : List F) (completion : ExactCompletion valid cost refines witness)
    (p : P) (hp : IsOptimum valid cost p) (b : Nat)
    (hsurvive : cost p ≤ b → ∃ f ∈ cover, refines p f) :
    (∃ f ∈ cover, cost (witness f) ≤ b) ↔ cost p ≤ b := by
  constructor
  · rintro ⟨f, _, hf⟩
    exact Nat.le_trans (hp.2 _ (completion.valid f)) hf
  · intro hb
    rcases hsurvive hb with ⟨f, hf, hpf⟩
    exact ⟨f, hf, Nat.le_trans (completion.minimum f p hp.1 hpf) hb⟩

theorem paid_precut_accounting (r m p : Nat) (hm : m = r + 1) (hp : m ≤ p) :
    r + (p - m) = p - 1 := by omega

theorem paid_tidied_accounting (r mLive pLive finished : Nat)
    (hm : mLive + finished = r + 1) (hp : mLive ≤ pLive) :
    r + (pLive - mLive) = (pLive + finished) - 1 := by omega

/-- If x and y are costs of two distinct local components, both cannot exceed
half of b when their sum is bounded by b. Local-to-global domination is external. -/
theorem unique_heavy_component (x y b : Nat) (hbudget : x + y ≤ b)
    (hx : b < 2 * x) : 2 * y ≤ b := by omega

theorem paid_depth_implies_half (r d b : Nat) (hpaid : r + d ≤ b)
    (hdepth : b ≤ 2 * r) : 2 * d ≤ b := by omega

theorem exact_target_squared_product : 25 * 23391 = 584775 := by decide
theorem exact_target_above_19 : ¬ (584775 * 100 < 361 * 160000) := by decide
theorem exact_target_below_baseline :
    584775 * 10000 * 10000 < 23391 * 23391 * 160000 := by decide

/-- Integer certificates: sqrt(2)<283/200, classical local base<483/200;
then (3/2)^2(483/200)<(7/3)^2 and 7/3<2.3391. Converting square
certificates to real square-root inequalities is an external ordered-field step. -/
theorem sqrt_two_upper_square : 2 * 200 * 200 < 283 * 283 := by decide
theorem weaker_product_square : 4347 * 9 < 49 * 800 := by decide
theorem weaker_certified_base_below_benchmark : 7 * 10000 < 3 * 23391 := by decide

#print axioms one_optimum_suffices
#print axioms conditional_decision_exact
#print axioms paid_precut_accounting
#print axioms paid_tidied_accounting
#print axioms unique_heavy_component
#print axioms paid_depth_implies_half
#print axioms exact_target_squared_product
#print axioms exact_target_above_19
#print axioms exact_target_below_baseline
#print axioms sqrt_two_upper_square
#print axioms weaker_product_square
#print axioms weaker_certified_base_below_benchmark

end BalancedSafeCover
