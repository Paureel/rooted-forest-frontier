import ProbeWork

namespace Universal233.RankConsumer
open RMAF CoreProgram SourceCoverage RankDichotomy CoreWork

def fourProbe (T : Tree) (color : Nat → Nat) : Receipt := generate T color 3

def fourAccepted (T : Tree) (color : Nat → Nat) : Bool := !(fourProbe T color).outputs.isEmpty

/-- The binary three-parent caller already knows its exact four input colors.
It passes literal budget3 and does not compute inputRank at runtime. -/
theorem four_accepted_iff (T : Tree) (color : Nat → Nat) (hs : (leaves T).Nodup)
    (hr : inputRank T color = 4) : fourAccepted T color = true ↔ RankFeasible T color := by
  have he : fourAccepted T color = accepted T color := by simp [fourAccepted,fourProbe,accepted,probe,hr]
  rw [he]
  exact accepted_iff T color hs

def optimizedFourOutputs (T : Tree) (color : Nat → Nat) (q : Nat) : List Output :=
  if q < 3 then [] else
    let p := fourProbe T color
    if p.outputs.isEmpty then (generate T color q).outputs else p.outputs

/-- Actual fixed-budget classification can reuse the unique cheap output.
Every literal output, including multiplicity/order, is preserved. -/
theorem optimized_four_exact (T : Tree) (color : Nat → Nat) (hs : (leaves T).Nodup)
    (hr : inputRank T color = 4) (q : Nat) :
    optimizedFourOutputs T color q = (generate T color q).outputs := by
  by_cases hq : q < 3
  · simp only [optimizedFourOutputs,hq,ite_true]
    symm
    exact below_rank_outputs_empty T color q (by omega)
  · cases he : (fourProbe T color).outputs with
    | nil => simp [optimizedFourOutputs,hq,he]
    | cons o os =>
      have ha : accepted T color = true := by
        have hprobe : probe T color = fourProbe T color := by simp [probe,fourProbe,hr]
        simp [accepted,hprobe,he]
      obtain ⟨z,hprobe,hcost,hall⟩ := accepted_literal_stable T color hs ha
      have hsame : o::os = [z] := by
        have hp : probe T color = fourProbe T color := by simp [probe,fourProbe,hr]
        simpa only [hp,he] using hprobe
      have hlarge : (generate T color q).outputs = [z] := by simpa [hr,hq] using hall q
      simpa [optimizedFourOutputs,hq,he,hsame] using hlarge.symm

theorem four_rejected_high (T : Tree) (color : Nat → Nat) (hs : (leaves T).Nodup)
    (hr : inputRank T color = 4) (h : fourAccepted T color = false)
    (q : Nat) (c : Rat) (hc : 2 ≤ c) :
    (∀ o, o ∈ (generate T color q).outputs → 4 ≤ o.sourceCuts.length) ∧
      rawQMass c (generate T color q).outputs ≤ 2*c^(-4 : Int) := by
  have he : fourAccepted T color = accepted T color := by simp [fourAccepted,fourProbe,accepted,probe,hr]
  have hmodel := rejected_cost_mass T color hs (by rw [←he];exact h) q c hc
  have hi : -((4 : Nat) : Int) = (-4 : Int) := by decide
  simpa only [hr,hi] using hmodel

/-- Frozen conservative source-model envelope; fixed guard/empty-test/call
setup and actual color callback bills are additional caller charges. -/
theorem four_probe_model_work (T : Tree) (color : Nat → Nat)
    (hr : inputRank T color = 4) :
    (meterGenerate T color 3).measured.work ≤ initialCharge T+64*(cap (inputResource T)+6) := by
  have h := probe_model_work T color (by omega)
  simpa only [hr] using h

theorem four_probe_color_calls (T : Tree) (color : Nat → Nat) :
    (meterGenerate T color 3).oracleCalls = if (leaves T).Nodup then (leaves T).length else 0 :=
  meterGenerate_calls T color 3
end Universal233.RankConsumer
