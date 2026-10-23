import Probe
import Work

namespace Universal233.RankConsumer
open RMAF CoreProgram SourceCoverage RankDichotomy CoreWork

/-- This is the frozen source MODEL envelope for an actual capped probe, not
an extracted fine-instruction identity. This bounds generate after its rank
argument is supplied; computing inputRank and color callback costs are additional. -/
theorem probe_model_work (T : Tree) (color : Nat → Nat) (hr : inputRank T color ≤ 4) :
    (meterGenerate T color (inputRank T color-1)).measured.work ≤
      initialCharge T+64*(cap (inputResource T)+6) := by
  let B := min (inputRank T color-1) ((leaves T).length-1)
  have hB : B ≤ 3 := by dsimp [B]; omega
  have hp : 2^(B+1) ≤ 16 := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (show B+1 ≤ 4 by omega)
    exact h
  have hm : (B+1)*2^(B+1) ≤ 64 := Nat.mul_le_mul (show B+1 ≤ 4 by omega) hp
  have h := generate_work_bound T color (inputRank T color-1)
  change _ ≤ initialCharge T+(cap (inputResource T)+6)*(B+1)*2^(B+1) at h
  calc
    _ ≤ initialCharge T+(cap (inputResource T)+6)*(B+1)*2^(B+1) := h
    _ = initialCharge T+(cap (inputResource T)+6)*((B+1)*2^(B+1)) := by rw [Nat.mul_assoc]
    _ ≤ initialCharge T+(cap (inputResource T)+6)*64 := Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _
    _ = initialCharge T+64*(cap (inputResource T)+6) := by rw [Nat.mul_comm _ 64]
end Universal233.RankConsumer
