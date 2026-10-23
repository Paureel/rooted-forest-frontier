import ColorClasses

namespace Universal233.RankConsumer
open RMAF CoreProgram SourceCoverage VertexGeometry RankDichotomy

def probe (T : Tree) (color : Nat → Nat) : Receipt := generate T color (inputRank T color-1)
def accepted (T : Tree) (color : Nat → Nat) : Bool := !(probe T color).outputs.isEmpty

theorem probe_nonempty_iff (T : Tree) (color : Nat → Nat) (hs : (leaves T).Nodup) :
    (probe T color).outputs ≠ [] ↔ RankFeasible T color := by
  constructor
  · intro hne
    obtain ⟨o,ho⟩ := List.exists_mem_of_ne_nil _ hne
    have hv := Assembly.generated_source_valid T color (inputRank T color-1) o ho
    have hm := CutRealization.generate_monochromatic T color (inputRank T color-1) o ho
    have hlen := generate_partition_cost T color _ o ho
    have hlo := generate_color_cost T color _ o ho
    have hhi := generate_output_budget T color _ o ho
    have hr := inputRank_pos T color
    change inputRank T color ≤ o.sourceCuts.length+1 at hlo
    exact ⟨o.partition,hv.1,hv.2,hm,by omega⟩
  · intro hf
    obtain ⟨o,ho,_⟩ := feasible_unique T color hs hf (inputRank T color-1) (Nat.le_refl _)
    change (generate T color (inputRank T color-1)).outputs ≠ []
    rw [ho]
    simp

theorem probe_empty_iff (T : Tree) (color : Nat → Nat) (hs : (leaves T).Nodup) :
    (probe T color).outputs = [] ↔ ¬RankFeasible T color := by
  constructor
  · intro he hf
    exact ((probe_nonempty_iff T color hs).2 hf) he
  · intro hn
    apply Classical.byContradiction
    intro hne
    exact hn ((probe_nonempty_iff T color hs).1 hne)

theorem accepted_iff (T : Tree) (color : Nat → Nat) (hs : (leaves T).Nodup) :
    accepted T color = true ↔ RankFeasible T color := by
  constructor
  · intro h
    apply (probe_nonempty_iff T color hs).1
    intro he
    simp [accepted,he] at h
  · intro hf
    have hn := (probe_nonempty_iff T color hs).2 hf
    cases he : (probe T color).outputs with
    | nil => exact False.elim (hn he)
    | cons o os => simp [accepted,he]

/-- One actual bounded probe identifies the very same literal output at ALL
larger budgets. No unknown partition is enumerated by this classifier. -/
theorem accepted_literal_stable (T : Tree) (color : Nat → Nat) (hs : (leaves T).Nodup)
    (h : accepted T color = true) :
    ∃ o, (probe T color).outputs = [o] ∧ o.sourceCuts.length = inputRank T color-1 ∧
      ∀ q, (generate T color q).outputs = if q < inputRank T color-1 then [] else [o] := by
  have hf := (accepted_iff T color hs).1 h
  obtain ⟨o,ho,hcost⟩ := feasible_unique T color hs hf (inputRank T color-1) (Nat.le_refl _)
  refine ⟨o,ho,hcost,?_⟩
  intro q
  by_cases hq : q < inputRank T color-1
  · simp only [hq,ite_true]
    exact below_rank_outputs_empty T color q hq
  · simp only [hq,ite_false]
    obtain ⟨z,hz,_⟩ := feasible_unique T color hs hf q (by omega)
    have homem : o ∈ (generate T color (inputRank T color-1)).outputs := by rw [ho]; simp
    have hmem := generate_outputs_mono T color (show inputRank T color-1 ≤ q by omega) o homem
    have he : o = z := by simpa only [hz,List.mem_singleton] using hmem
    simpa only [←he] using hz

theorem rejected_cost_mass (T : Tree) (color : Nat → Nat) (hs : (leaves T).Nodup)
    (h : accepted T color = false) (q : Nat) (c : Rat) (hc : 2 ≤ c) :
    (∀ o, o ∈ (generate T color q).outputs → inputRank T color ≤ o.sourceCuts.length) ∧
      rawQMass c (generate T color q).outputs ≤ 2*c^(-(inputRank T color : Int)) := by
  have hn : ¬RankFeasible T color := by
    intro hf
    have he := (accepted_iff T color hs).2 hf
    simp [h] at he
  exact ⟨fun o ho => infeasible_cost T color q hn o ho,infeasible_mass T color q hn c hc⟩

theorem probe_budget_le_three (T : Tree) (color : Nat → Nat) (hr : inputRank T color ≤ 4) :
    inputRank T color-1 ≤ 3 := by omega
end Universal233.RankConsumer
