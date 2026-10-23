import SelectorConsumer
namespace Universal233.Rule5PaidSelector.Controls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Rule5Case322 Rule5Local Rule5Local.Pre Rule5Classification Rule5FinalClassification Case322Extraction Case322PaidGuard
set_option maxRecDepth 24000
set_option maxHeartbeats 800000

def d : BadSelection := ⟨[false,false,true],[false,true],2⟩
def u : RMAF.Vertex := [false,true]
def v : RMAF.Vertex := [false,false,false,true]
example : selectFinal sixT sixS 0 1=some (.remaining d (.second u v)) := by decide
example : (buildSelected sixT sixS 0 1).isSome=true := by decide
example : (buildSelected sixT sixS 0 1).map (fun R => decide (R.d=d) && decide (R.u=u) && decide (R.v=v) &&
 decide (R.geometry.a=0) && decide (R.geometry.b=1) && decide (R.geometry.c=2) &&
 decide (R.geometry.r=v) && decide (R.geometry.uc=u) && decide (leaves R.geometry.X=[14,15,16]))=some true := by decide
example : ((buildSelected sixT sixS 0 1).map (fun R =>
 (guardedPlan R.geometry).all (currentGuard sixT sixS)))=some true := by decide

def mirror : Tree → Tree
 | .leaf x => .leaf x
 | .node l r => .node (mirror r) (mirror l)
example : (buildSelected (mirror sixT) (mirror sixS) 1 0).isSome=true := by decide
example : (buildForSecond sixT sixS 0 1 d v u).isSome=false := by decide
example : (buildForSecond sixT sixS 0 1 ⟨d.badArc,d.singletonArc,99⟩ u v).isSome=false := by decide
example : parseBottom sixS [] false false false 1 0 2=none := by decide

def omittedRows : List BottomData := (rows sixS 0 1 2).filter (fun R => decide (R.w≠[]))
example : (omittedRows.findSome? (buildOne sixT sixS 0 1 d u v)).isSome=false := by decide
example : (rows sixS 0 1 2).length≤16*(HardParent.vertices sixS).length := by decide
example : ([false,true].all fun sa => [false,true].all fun sc => [false,true].all fun sb =>
 parseBottom (bottom sa sc sb 0 1 2 (.leaf 9)) [] sa sc sb 0 1 2==some (.leaf 9))=true := by decide
example : buildSelected (.leaf 0) (.leaf 0) 0 1=none := by decide

-- Actual selector hypotheses are available without a geometry input.
example : ∃R, buildSelected sixT sixS 0 1=some R ∧ R.d=d ∧ R.u=u ∧ R.v=v :=
 buildSelected_complete (i:=[false,false,false,true]) rfl (by decide) (by decide)
end Universal233.Rule5PaidSelector.Controls
