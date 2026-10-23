import SelectedInterfaces
import Rule5PreControls
namespace Universal233.Rule5OrdinaryDispatch.Controls
open RMAF CherryBranching Rule5Local Rule5Local.Pre Rule5Classification Rule5FinalClassification
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
def tag : Option FinalSelection → Nat
 | some (.prefix (.large _)) => 1
 | some (.prefix (.two _)) => 2
 | some (.prefix (.outside _)) => 3
 | some (.remaining _ (.first _ _)) => 4
 | some (.remaining _ (.third _ _)) => 5
 | some (.remaining _ (.one _)) => 6
 | some (.remaining _ (.second _ _)) => 7
 | _ => 0
def emptyCallback : Ordinary := fun _ _ _ => none
def fixtures : List (Tree×Tree×Nat) :=
 [(largeT,largeS,1),(twoT,twoS,2),(outsideT,outsideS,3),
  (firstT,firstS,4),(thirdT,thirdS,5),(commonT,commonS,6),(sixT,sixS,7)]
def sourceJobs (T S : Tree) (q : Nat) : List ForestJob :=
 match selectFinal T S 0 1 with
 | none => []
 | some z => forestJobs T q (selectedForestChildren S 0 1 z)
def selectorsPass : Bool := fixtures.all fun f => tag (selectFinal f.1 f.2.1 0 1)==f.2.2
def zeroBudgetPass : Bool := fixtures.all fun f => dispatch emptyCallback f.1 f.2.1 0 1 0==.answered none
def belowPaidPass : Bool :=
 [largeS,twoS,outsideS].all fun S =>
  (remaining 1 (pendantChild S 0 1)).isNone
def tracePass : Bool := fixtures.all fun f =>
 (sourceJobs f.1 f.2.1 6).all fun j =>
  decide (j.residual<6) && decide (j.residual+j.child.paid=6) &&
  decide (j.sources=j.child.sourceForest) && decide (j.target=some f.1)
def vectorsPass : Bool := fixtures.all fun f =>
 match selectFinal f.1 f.2.1 0 1 with
 | none => false
 | some z =>
   let v := (selectedForestChildren f.2.1 0 1 z).map Child.paid
   match f.2.2 with
   | 1 => v==[2]
   | 2 | 3 => v==[2,2,2,2,2]
   | 4 | 5 => v==[1,2]
   | _ => v==[]
def roleSwapPass : Bool := tag (selectFinal sixT sixS 1 0)==7 &&
 (Rule5PaidSelector.buildSelected sixT sixS 1 0).isSome
def allControls : Bool := selectorsPass && zeroBudgetPass && belowPaidPass && tracePass && vectorsPass && roleSwapPass
theorem true_controls : allControls=true := by decide
#eval ("fresh_controls",selectorsPass,zeroBudgetPass,belowPaidPass,tracePass,vectorsPass,roleSwapPass)
#eval fixtures.map fun f => (f.2.2,tag (selectFinal f.1 f.2.1 0 1),
  (sourceJobs f.1 f.2.1 6).map fun j => (j.child.paid,j.residual,j.sources.length))
end Universal233.Rule5OrdinaryDispatch.Controls
