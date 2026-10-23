import Std
namespace NormalizationRepair

/-- Cardinal accounting for the two exchanges in source Lemma6.10.
The number of second-stage cuts is the actual number, not a prefix count.
All links from graph cutsets to these counts remain explicit obligations. -/
theorem two_exchange_cost_le
    (base p₁ p₂ p₃ added restore₁ removed₂ restore₂ : Nat)
    (hp₂ : p₂ ≤ 2) (hp₃ : 1 ≤ p₃)
    (hprefix : 2 ≤ p₁ + p₂ + p₃)
    (hadded : added + p₂ ≤ 2)
    (hr₁ : restore₁ ≤ 1)
    (hfirst : p₃ = 1 → restore₁ = 0)
    (hsecond₁ : p₃ = 1 → p₁ ≤ removed₂)
    (hsecond₂ : 2 ≤ p₃ → 1 ≤ removed₂)
    (hr₂ : restore₂ ≤ 1)
    (hsecondSmall : removed₂ ≤ 1 → restore₂ = 0)
    (havailable₁ : p₃ ≤ base + added)
    (havailable₂ : removed₂ ≤ base + added - p₃ + restore₁) :
    base + added - p₃ + restore₁ - removed₂ + restore₂ ≤ base := by
  by_cases hp : p₃ = 1
  · have hf := hfirst hp
    have hs := hsecond₁ hp
    by_cases hsmall : removed₂ ≤ 1
    · have hz := hsecondSmall hsmall
      omega
    · omega
  · have hlarge : 2 ≤ p₃ := by omega
    have hs := hsecond₂ hlarge
    by_cases hsmall : removed₂ ≤ 1
    · have hz := hsecondSmall hsmall
      omega
    · omega

#print axioms two_exchange_cost_le
end NormalizationRepair
