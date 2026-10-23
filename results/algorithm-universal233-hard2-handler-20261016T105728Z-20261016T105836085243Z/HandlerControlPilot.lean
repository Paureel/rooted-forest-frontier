import OrdinaryPrepareBound
open RMAF Universal233 WholeSourceWork CoreWork OrdinaryDispatch.Hard2SourceWork
namespace HandlerPilot
 def cross : Tree:=.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
 def T : Tree:=.node cross (.leaf 4)
 def S : Tree:=.node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.leaf 4)
 def refused : GenericForest.FrontierWork.Ordinary:=fun _ _ _=>none
 #eval let r:=goodPairLocalSource refused T S [0,1] [2,3] [4] 3
   (r.value.answer.map List.length,r.value.calls.map fun a=>(ForestState.labels a.target,a.sources.map leaves,a.budget))
 #eval let r:=goodPairLocalSource refused T S [0,1] [2,3] [4] 2
   (r.value.answer.map List.length,r.value.calls.map fun a=>a.budget)
 #eval (ordinarySlotMeter (.leaf 0) (.leaf 0) [0]).value
end HandlerPilot
