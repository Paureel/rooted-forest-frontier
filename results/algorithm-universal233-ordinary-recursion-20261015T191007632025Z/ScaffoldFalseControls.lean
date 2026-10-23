import ScaffoldControls
open RMAF ForestState OrdinaryScaffold OrdinaryScaffold.Controls OrdinaryDispatch
example : (OrdinaryScaffold.solve 1 T S).map (fun F=>(agreement T S F,F.length))=some (true,3) := by cbv
example : (OrdinaryScaffold.solve 2 T S).map (fun F=>(agreement T S F,F.length))=some (true,2) := by cbv
example : (leaves (contract c.a c.b (commonFresh graftT) graftT)).length=(leaves graftT).length := by decide
