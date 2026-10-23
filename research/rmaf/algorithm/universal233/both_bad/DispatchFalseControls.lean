import DispatchControls
namespace Universal233.BothBad.DispatchControls
theorem bad_free_paid_one : ((run 5).calls.map Call.budget)=[2,1,1] := by decide
theorem bad_whole_B_tree : ((run 5).calls.map (fun c => c.sources.length))=[1,1,1] := by decide
theorem bad_unpaid_global_budget : (run 4).answer.isSome=true := by decide
end Universal233.BothBad.DispatchControls
