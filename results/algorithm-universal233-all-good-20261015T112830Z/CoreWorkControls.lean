import Payload
import Primitive

namespace Universal233.CoreWork.Controls
open RMAF CoreProgram CoreProgram.Controls

/-- Eight leaves, maximally unbalanced, built independently of the evaluator. -/
def caterpillar : Nat → Tree
  | 0 => .leaf 0
  | n+1 => .node (caterpillar n) (.leaf (n+1))

def sampleOutput : Output := ⟨[[0]],[]⟩
def appendFixture : Receipt := ⟨List.replicate 4 sampleOutput,List.replicate 3 "refusal",0,0,0⟩

theorem singleton_oracle : (meterGenerate (.leaf 7) id 0).oracleCalls = 1 := by decide

theorem singleton_no_cut : (meterGenerate (.leaf 7) id 0).measured.prunedCalls = 0 := by decide

theorem homogeneous_caterpillar_copies :
    normalizeWork (fromTree (fun _ => 0) [] (caterpillar 7)) = 92 := by decide

theorem homogeneous_caterpillar_output :
    (meterGenerate (caterpillar 7) (fun _ => 0) 7).measured.receipt.outputs.length = 1 := by decide

theorem unbalanced_eight_oracles :
    (meterGenerate (caterpillar 7) (fun _ => 0) 7).oracleCalls = 8 := by decide

theorem alternating_has_real_copy :
    1 ≤ (meterGenerate crossed parity 3).measured.copied := by decide

theorem budget_zero_keeps_pruned :
    (meterGenerate crossed parity 0).measured.prunedCalls = 2 := by decide

theorem budget_zero_keeps_attempts :
    (meterGenerate crossed parity 0).measured.receipt.childAttempts = 2 := by decide

theorem duplicate_no_oracle :
    (meterGenerate (.node (.leaf 1) (.leaf 1)) id 3).oracleCalls = 0 := by decide

theorem duplicate_refusal :
    (meterGenerate (.node (.leaf 1) (.leaf 1)) id 3).measured.receipt.refusals =
      ["duplicate original label"] := by decide

theorem append_real_cells : appendCells appendFixture = 7 := by decide

theorem huge_budget_capped :
    (meterGenerate crossed parity 1000000).measured.work =
      (meterGenerate crossed parity 3).measured.work := by decide

end Universal233.CoreWork.Controls
