import ColorClasses
namespace Universal233.RankConsumer.Controls
open RMAF CoreProgram SourceCoverage RankDichotomy

def contiguous : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossed : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def two (x : Nat) : Nat := if x<2 then 0 else 1

theorem contiguous_probe : (generate contiguous two (inputRank contiguous two-1)).outputs.map
    (fun o => o.sourceCuts.length) = [1] := by decide
theorem crossed_probe : (generate crossed two (inputRank crossed two-1)).outputs = [] := by decide
theorem crossed_larger : (generate crossed two 3).outputs.map (fun o => o.sourceCuts.length) = [2,2] := by decide
theorem three_probe : (generate (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) id 2).outputs.map
    (fun o => o.sourceCuts.length) = [2] := by decide
theorem one_qzero : (generate (.leaf 0) (fun _ => 0) 0).outputs.map (fun o => o.sourceCuts.length) = [0] := by decide
def repeated : Tree := .node (.leaf 0) (.leaf 0)
theorem repeated_refusal : (generate repeated (fun _ => 0) 0).outputs = [] := by decide
theorem repeated_bare_feasible : RankFeasible repeated (fun _ => 0) := by
  refine ⟨[[0]],by decide,by decide,?_,by decide⟩
  intro b hb x y hx hy
  rfl
end Universal233.RankConsumer.Controls
