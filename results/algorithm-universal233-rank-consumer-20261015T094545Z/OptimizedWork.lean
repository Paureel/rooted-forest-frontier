import FourProbe

namespace Universal233.RankConsumer
open RMAF CoreProgram SourceCoverage RankDichotomy CoreWork

structure MeasuredProbe where
  outputs : List Output
  work : Nat
  colorCalls : Nat

def fullCoreBound (T : Tree) (q : Nat) : Nat := initialCharge T+
  (cap (inputResource T)+6)*(min q ((leaves T).length-1)+1)*2^(min q ((leaves T).length-1)+1)
def fixedProbeBound (T : Tree) : Nat := initialCharge T+64*(cap (inputResource T)+6)

/-- Actual caller branch evaluator; 64 is a declared fixed scalar source
allowance, not an extracted instruction count. Color evaluation bill is extra. -/
def meterOptimizedFour (T : Tree) (color : Nat → Nat) (q : Nat) : MeasuredProbe :=
  if q<3 then ⟨[],64,0⟩ else
    let p := meterGenerate T color 3
    if p.measured.receipt.outputs.isEmpty then
      let g := meterGenerate T color q
      ⟨g.measured.receipt.outputs,64+p.measured.work+g.measured.work,p.oracleCalls+g.oracleCalls⟩
    else ⟨p.measured.receipt.outputs,64+p.measured.work,p.oracleCalls⟩

@[simp] theorem meterOptimizedFour_value (T : Tree) (color : Nat → Nat) (q : Nat) :
    (meterOptimizedFour T color q).outputs = optimizedFourOutputs T color q := by
  by_cases hq : q<3
  · simp [meterOptimizedFour,optimizedFourOutputs,hq]
  · by_cases he : (generate T color 3).outputs.isEmpty = true
    <;> simp [meterOptimizedFour,optimizedFourOutputs,hq,fourProbe,meterGenerate_receipt,he]

theorem meterOptimizedFour_calls (T : Tree) (color : Nat → Nat) (q : Nat) :
    (meterOptimizedFour T color q).colorCalls =
      if q<3 then 0 else
      if (fourProbe T color).outputs.isEmpty then
        2*(if (leaves T).Nodup then (leaves T).length else 0)
      else if (leaves T).Nodup then (leaves T).length else 0 := by
  simp only [meterOptimizedFour]
  split
  · rfl
  · simp only [meterGenerate_receipt,meterGenerate_calls,fourProbe]
    split <;> simp_all [Nat.two_mul]

theorem meterOptimizedFour_bound (T : Tree) (color : Nat → Nat) (q : Nat)
    (hr : inputRank T color = 4) :
    (meterOptimizedFour T color q).work ≤
      if q<3 then 64 else 64+fixedProbeBound T+
        if (fourProbe T color).outputs.isEmpty then fullCoreBound T q else 0 := by
  have hp := four_probe_model_work T color hr
  change (meterGenerate T color 3).measured.work ≤ fixedProbeBound T at hp
  have hq := generate_work_bound T color q
  change (meterGenerate T color q).measured.work ≤ fullCoreBound T q at hq
  unfold meterOptimizedFour
  split
  · simp_all
  · simp only [meterGenerate_receipt,fourProbe]
    split <;> simp_all <;> omega
end Universal233.RankConsumer
