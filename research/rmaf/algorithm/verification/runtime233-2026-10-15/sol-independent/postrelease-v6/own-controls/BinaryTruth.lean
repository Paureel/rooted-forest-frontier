import BinaryCallerOrdinaryBounds
open GenericForest.BinaryProvider GenericForest.BinaryCaller GenericForest.ScalarBits
private def z : GenericForest.BinaryProvider.Tree := .leaf []
private def bad : GenericForest.BinaryProvider.Forest := [[]]
example : decode [false,true,false,true]=10 := by decide +kernel
example : (payBudget [false,true,false,true] [(),(),(),()]).value=[false,true,true,false] := by decide +kernel
example : (payBudget [false,true,false,true] [(),(),(),()]).value.length=4 := by decide +kernel
example : (flattenAnswers [(0,([]:GenericForest.BinaryProvider.Forest)),(1,[])]).work=11 := by decide +kernel
example : (checkOptional (some z) [z] [] none).work=1 := by decide +kernel
example : (disjointFinish z [z] [] (none:Option (List (Nat×GenericForest.BinaryProvider.Forest)))).work=1 := by decide +kernel
example : setupCallsWork (some z) [z] [] [bad,bad]=2*(checkerCapacity (some z) [z] [] bad).work := by decide +kernel
example : (bestCandidates (some z) [z] [] [[[[]]],[[[]]]]).value.isSome=true := by decide +kernel
