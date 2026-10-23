import ExecutionFacts
namespace Universal233.BothBad
open RMAF CoreProgram ForestState RestrictionBridge

/-- Explicit induction hypothesis for a future exact forest solver at one
literal call. No implementation, termination or runtime is asserted here. -/
def ExactAt (solve : ForestSolver) (t : Option Tree) (ss : List Tree) (b : Nat) : Prop :=
  (∀ H, solve t ss b=some H → agrees t ss H=true ∧ additionalCost ss H≤b ∧
    ∀ F, agrees t ss F=true → additionalCost ss H≤additionalCost ss F) ∧
  (∀ F, agrees t ss F=true → additionalCost ss F≤b → ∃ H, solve t ss b=some H)

theorem exactAt_residual (solve : ForestSolver) (t : Option Tree) (ss : List Tree) (b : Nat)
    (IH : ExactAt solve t ss b) : ForestGroups.ResidualSolverContract solve t ss b := by
  intro hp
  constructor
  · constructor
    · intro hn F hF
      by_cases hb : additionalCost ss F≤b
      · obtain ⟨H,hH⟩ := IH.2 F hF hb
        simp [hn] at hH
      · omega
    · intro hn
      cases hr : solve t ss b with
      | none => rfl
      | some H =>
        have hs := IH.1 H hr
        have := hn H hs.1
        omega
  · intro H hH
    exact ⟨(IH.1 H hH).1,(IH.1 H hH).2.1⟩

/-- Actual generated Q may overlap on the target. The callback is made on the
materialized source FOREST and retains all target agreement checks. -/
theorem full_candidate (solve : ForestSolver) (T S : Tree) (color : Nat → Nat)
    (o : Output) (q0 b : Nat) (F : Forest)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves T ↔ x∈leaves S)
    (ho : o∈(generate S color q0).outputs)
    (hF : agreement T S F=true) (href : Refines F o.partition)
    (hbudget : F.length-o.partition.length≤b)
    (IH : ExactAt solve (some T) (OutputState.sourceForest S o.partition) b) :
    ∃ H, (dispatch solve T S ⟨o,.full,b⟩).answer=some H ∧
      agreement T S H=true ∧ Refines H o.partition ∧
      H.length-o.partition.length≤b ∧ H.length≤F.length := by
  obtain ⟨hQ,eQ⟩ := Assembly.generated_source_valid S color q0 o ho
  have fstate := OutputState.original_to_state T S o.partition F ht hs same hQ hF href
  have ce := OutputState.exact_additional_cost S o.partition F hs hQ
  obtain ⟨H,hH⟩ := IH.2 F fstate (by rw [ce];exact hbudget)
  obtain ⟨hstate,hb,hmin⟩ := IH.1 H hH
  obtain ⟨hAF,hRef⟩ := OutputState.state_to_original T S o.partition H hs same hQ eQ hstate
  have ch := OutputState.exact_additional_cost S o.partition H hs hQ
  have hmin' := hmin F fstate
  have hfLen := ForestGroups.sources_le_blocks (some T) (OutputState.sourceForest S o.partition) F fstate
  have hmat := (OutputState.checked_materialization S o.partition hs hQ).1
  refine ⟨H,?_,hAF,hRef,?_,?_⟩
  · simpa only [dispatch] using hH
  · rwa [ch] at hb
  · rw [ch,ce] at hmin'
    rw [hmat] at hfLen
    omega

end Universal233.BothBad
