import BOConditional
namespace OrdinaryDispatch.BudgetOptimization.Controls
open RMAF Universal233

def summary (r : Execution) :=
 (r.search.selected.map Prod.fst,
  r.search.trials.map (fun t => (t.1,t.2.isSome)),
  r.recoveries.length,
  r.output.map (fun o => (o.sourceCuts.length,o.partition.length)))

def tripleT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def tripleS : Tree := .node (.leaf 0) (.node (.leaf 1) (.leaf 2))

theorem singleton : summary (optimize (.leaf 7) (.leaf 7))=
 (some 0,[(0,true)],1,some (0,1)) := by decide +kernel

theorem identical : summary (optimize (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))=
 (some 0,[(0,true)],1,some (0,1)) := by decide +kernel

theorem triple_failed_retained : summary (optimize tripleT tripleS)=
 (some 1,[(0,false),(1,true)],1,some (1,2)) := by decide +kernel

theorem quartet_failed_retained : summary (optimize leftTree rightTree)=
 (some 1,[(0,false),(1,true)],1,some (1,2)) := by decide +kernel

theorem repeated_malformed : summary (optimize (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))=
 (none,[],0,none) := by decide +kernel

theorem unequal_malformed : summary (optimize (.leaf 0) (.leaf 1))=
 (none,[],0,none) := by decide +kernel

theorem external_zero : FastOrdinary.external (.leaf 7) (.leaf 7) 0=none := rfl

def synthetic (q : Nat) : Option CommonForest := if q=1 then some [[0]] else none

theorem synthetic_trace : (scan synthetic 0 3).trials=[(0,none),(1,some [[0]])] := by decide +kernel

theorem all_refused : (scan (fun _ => none) 0 3).trials=[(0,none),(1,none),(2,none)] ∧
 (scan (fun _ => none) 0 3).selected=none := by decide +kernel

theorem full_bill : trialWork (fun q => 2^q) (scan synthetic 0 3).trials=3 := by decide +kernel

theorem positive_conversion : ((optimize (.leaf 7) (.leaf 7)).output.map
 (fun o => o.sourceCuts.length+1=o.partition.length))=some True := by decide +kernel

#eval summary (optimize (.leaf 7) (.leaf 7))
#eval summary (optimize tripleT tripleS)
#eval summary (optimize leftTree rightTree)
#eval summary (optimize (.leaf 0) (.leaf 1))
end OrdinaryDispatch.BudgetOptimization.Controls
