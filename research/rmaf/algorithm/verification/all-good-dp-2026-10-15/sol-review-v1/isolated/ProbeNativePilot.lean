import NativeAdapter
open RMAF ForestState AllGoodDP
open SolNative
#eval emit "STATE" (stateRecord "none-empty" none [] [0,1,2,1000000000])
#eval emit "STATE" (stateRecord "none-nonempty" none [(.leaf 9)] [0,1,2,1000000000])
#eval emit "STATE" (stateRecord "leaf9" (some (.leaf 9)) [(.leaf 9)] [0,1,2,1000000000])
