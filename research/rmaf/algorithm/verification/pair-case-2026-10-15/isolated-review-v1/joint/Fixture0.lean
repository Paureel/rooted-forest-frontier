import ActualReadout
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open FreshActualReadout
def suppliedPartitions : List (List (List Nat)) := [[[1],[2],[3],[4]],[[1,2],[3],[4]],[[1,3],[2],[4]],[[1,4],[2],[3]],[[1],[2,3],[4]],[[1,2,3],[4]],[[1,4],[2,3]],[[1],[2,4],[3]],[[1,2,4],[3]],[[1,3],[2,4]],[[1],[2],[3,4]],[[1,2],[3,4]],[[1,3,4],[2]],[[1],[2,3,4]],[[1,2,3,4]]]
#eval IO.println ("FRESH_READOUT|" ++ (fixtureRows "binary_tiny" (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) (.node (.node (.leaf 1) (.leaf 3)) (.node (.leaf 2) (.leaf 4))) [1,2,3,4] [1,2] [3,4] [[1,2],[3,4]] suppliedPartitions).compress)
