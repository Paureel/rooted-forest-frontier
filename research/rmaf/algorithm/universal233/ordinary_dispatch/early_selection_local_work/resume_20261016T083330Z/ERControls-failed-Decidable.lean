import ERInterface
import EarlyControls
namespace OrdinaryDispatch.EarlyLocalWork.Controls
open RMAF Universal233 WholeSourceWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.FastOrdinary.Controls
open Rule5Local.Pre
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

def triT : Tree:=.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def triS : Tree:=.node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def malformed : Tree:=.node (.leaf 7) (.leaf 7)
def ptag : DepthOne.Result→Nat
 | .refused=>0 | .found none=>1 | .found (some _)=>2 | .rejected=>3
def pretrace (T S : Tree) := meterBest DepthOne.cutCost (meterCandidate T S) (DepthOne.candidates S)
def toy := meterBest id (fun n:Nat=>⟨decide (n≤2),1⟩) [2,1,3]

theorem ordinary_control :
 [(meterOrdinaryProper (.leaf 7) (.leaf 7)).value,
  (meterOrdinaryProper triT triT).value,
  (meterOrdinaryProper malformed malformed).value,
  (meterOrdinaryProper (.leaf 7) (.leaf 8)).value]=[true,true,false,false] := by decide

theorem pretest_controls :
 [ptag (meterPretest (.leaf 7) (.leaf 7)).value,
  ptag (meterPretest triT triT).value,
  ptag (meterPretest quartetT quartetS).value,
  ptag (meterPretest triT triS).value,
  ptag (meterPretest malformed malformed).value]=[1,1,3,2,0] := by decide

theorem crossed_all_failures :
 (pretrace quartetT quartetS).checks.map Prod.snd=List.replicate 7 false ∧
 (pretrace quartetT quartetS).tailSizes=[6,5,4,3,2,1,0] ∧
 (pretrace quartetT quartetS).value=none := by decide

theorem tri_all_tails : (pretrace triT triS).checks.length=5 ∧
 (pretrace triT triS).tailSizes=[4,3,2,1,0] := by decide

theorem toy_trace : toy.value=some 1 ∧ toy.work=24 ∧
 toy.checks=[(2,true),(1,true),(3,false)] ∧ toy.tailSizes=[2,1,0] ∧
 toy.comparisons=[(2,1)] := by decide

theorem empty_selector_and_exact_bill :
 (meterSelect (.leaf 7) (.leaf 7)).value=none ∧
 (meterSelect (.leaf 7) (.leaf 7)).work=16 := by decide

theorem orientation_controls :
 [(graftT,graftS),(oneT,oneS),(oneS,oneT),(highT,highS),
  (highT,reverseHighS),(quartetT,quartetS),(sixT,sixS)].map
  (fun p=>OrdinaryDispatch.FastOrdinary.Controls.etag (meterEarly p.1 p.2).value)=[1,3,4,5,6,7,9] := by decide

theorem rule4_orientations :
 [(meterRule4Select quartetT quartetS).value.isSome,
  (meterRule4Select quartetS quartetT).value.isSome,
  (meterRule4Select sixT sixS).value.isSome,
  (meterRule4Select sixS sixT).value.isSome]=[true,true,false,false] := by decide

theorem large_current_budget :
 (match (meterFront 1000 (.leaf 7) (.leaf 7)).value with
  | .stop x=>x=some [[7]] | .selected _=>False) ∧
  ¬(1000≤(leaves (.leaf 7)).length) := by decide

#eval ("ordinary",[(meterOrdinaryProper (.leaf 7) (.leaf 7)).value,(meterOrdinaryProper malformed malformed).value])
#eval ("pretest",[ptag (meterPretest (.leaf 7) (.leaf 7)).value,ptag (meterPretest quartetT quartetS).value,ptag (meterPretest triT triS).value])
#eval ("crossed",(pretrace quartetT quartetS).checks.map Prod.snd,(pretrace quartetT quartetS).tailSizes)
#eval ("toy",toy.value,toy.work,toy.tailSizes,toy.comparisons)
#eval ("orientations",[(graftT,graftS),(oneT,oneS),(oneS,oneT),(highT,highS),(highT,reverseHighS),(quartetT,quartetS),(sixT,sixS)].map (fun p=>OrdinaryDispatch.FastOrdinary.Controls.etag (meterEarly p.1 p.2).value))
#eval ("primitive_work_leaf",(meterSelect (.leaf 7) (.leaf 7)).work)
end OrdinaryDispatch.EarlyLocalWork.Controls
