import BindingControls
namespace Universal233.BothBadGrouped.Controls
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap
open ForestState ForestGroups RestrictionBridge PaidQueries GroupedFullQuery
example : 6-cheap.sourceCuts.length=4 := by decide
example : b∈cheap.partition := by decide
example : omitCTrace.map Prod.snd=[2] := by rw [omitted_trace];decide
example : (6-(omitCTrace.map Prod.snd).headD 99)=4 := by rw [omitted_trace];decide
end Universal233.BothBadGrouped.Controls
