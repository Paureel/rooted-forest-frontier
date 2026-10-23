import Std

/- GLOBAL-CB2: explicit finite constraint implications used at compile_children.
   Original-tree C1 correspondence and a universal state bound are separate. -/
namespace ConstraintCompression

def Hits (cuts row : List Nat) : Prop :=
  ∃ e, e ∈ row ∧ e ∈ cuts

def Satisfies (rows : List (List Nat)) (cuts : List Nat) : Prop :=
  ∀ row ∈ rows, Hits cuts row

def RowImplies (stronger weaker : List (List Nat)) : Prop :=
  ∀ row ∈ weaker, ∃ small ∈ stronger, small ⊆ row

theorem rowImplicationSound (stronger weaker : List (List Nat))
    (cuts : List Nat) (subsumes : RowImplies stronger weaker)
    (satisfied : Satisfies stronger cuts) : Satisfies weaker cuts := by
  intro row hr
  obtain ⟨small, hs, hsub⟩ := subsumes row hr
  obtain ⟨e, he, hc⟩ := satisfied small hs
  exact ⟨e, hsub he, hc⟩

theorem independentUnionFeasible (a b : List (List Nat))
    (ka kb : List Nat) (ha : Satisfies a ka) (hb : Satisfies b kb) :
    Satisfies (a ++ b) (ka ++ kb) := by
  intro row hr
  cases List.mem_append.mp hr with
  | inl hm =>
    obtain ⟨e, he, hk⟩ := ha row hm
    exact ⟨e, he, List.mem_append_left kb hk⟩
  | inr hm =>
    obtain ⟨e, he, hk⟩ := hb row hm
    exact ⟨e, he, List.mem_append_right ka hk⟩

theorem dominatedResidualWitness (a b : List (List Nat))
    (cuts : List Nat) (weaker : RowImplies b a)
    (valid : Satisfies b cuts) : Satisfies a cuts :=
  rowImplicationSound b a cuts weaker valid

theorem prefixCostSubstitution (left right witness : List Nat)
    (cheaper : left.length ≤ right.length) :
    (left ++ witness).length ≤ (right ++ witness).length := by
  simp only [List.length_append]
  omega

/- Literal projected residual edge-mask rows of the frozen quotient-star
   original pair. This finite computation certifies the stated CB2 diagnostic;
   the Python-to-original-tree interpretation is not asserted by this theorem. -/
def starChildren : Array (List Nat) := #[
  [116,436,692,724,740,752,788,868,880,932,944,960],
  [96,416,672,960],
  [81,401,657,705,720,769,848,912,960],
  [77,397,709,713,716,773,841,844,905,908,960]
]

def impliesBits (stronger weaker : List Nat) : Bool :=
  weaker.all (fun h => stronger.any (fun g => Nat.land g h == g))

theorem starChildrenPairwiseIncomparable :
    ∀ i : Fin 4, ∀ j : Fin 4, i ≠ j →
      impliesBits starChildren[i] starChildren[j] = false := by
  decide

theorem fourUnitBenchmarkMassFailure : 4 * 10000 > 23391 := by decide

theorem fourUnitLicensedMassFailure : 4 * 2 > 3 := by decide

theorem twoUnitBenchmarkMassPass : 2 * 10000 < 23391 := by decide

#print axioms rowImplicationSound
#print axioms independentUnionFeasible
#print axioms dominatedResidualWitness
#print axioms prefixCostSubstitution
#print axioms starChildrenPairwiseIncomparable
#print axioms fourUnitBenchmarkMassFailure
#print axioms fourUnitLicensedMassFailure
#print axioms twoUnitBenchmarkMassPass

end ConstraintCompression
