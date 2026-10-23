import CutoffFacts
import Rule5PreControls
namespace OrdinaryDispatch.FastOrdinary.Controls
open RMAF ForestState Universal233 Universal233.CherryBranching Rule5Local.Pre
set_option maxRecDepth 8000
def quartetT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def quartetS : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def graftT : Tree := .node (.node (.leaf 4) (.leaf 5)) quartetT
def graftS : Tree := .node (.node (.leaf 4) (.leaf 5)) quartetS
def oneT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def oneS : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)) (.leaf 3)
def highT : Tree := .node (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 4)) (.leaf 5)) (.leaf 3)
def highS : Tree := .node (.node (.node (.node (.node (.leaf 2) (.leaf 3)) (.leaf 0)) (.leaf 4)) (.leaf 5)) (.leaf 1)
def reverseHighS : Tree := .node (.node (.node (.node (.node (.leaf 2) (.leaf 3)) (.leaf 0)) (.leaf 4)) (.leaf 1)) (.leaf 5)
def etag {T S : Tree} : Early T S→Nat
 | .common false _ => 1 | .common true _ => 2
 | .one false _ => 3 | .one true _ => 4
 | .high false _ => 5 | .high true _ => 6
 | .rule4Forward _ => 7 | .rule4Reverse _ => 8
 | .hard2 _ _ => 9 | .refused => 0
def stag : Option (Priority×Candidate)→Nat
 | some (.common,_) => 1 | some (.one,_) => 2
 | some (.high,_) => 3 | some (.hard2,_) => 4 | none => 0
def examples : List (Tree×Tree) :=
 [(graftT,graftS),(oneT,oneS),(oneS,oneT),(highT,highS),(highT,reverseHighS),
  (quartetT,quartetS),(sixT,sixS),(sixS,sixT),(firstT,firstS),(thirdT,thirdS)]
#eval examples.map fun p => (stag (select p.1 p.2),stag (select p.2 p.1),etag (early p.1 p.2))
theorem forward_common : etag (early graftT graftS)=1 := by decide
theorem actual_rule4 : etag (early quartetT quartetS)=7 := by decide
theorem actual_rule4_both_orientations : (Rule4.select quartetT quartetS).isSome=true ∧
 (Rule4.select quartetS quartetT).isSome=true := by decide
theorem actual_hard2 : etag (early sixT sixS)=9 := by decide
theorem actual_forward_one : etag (early oneT oneS)=3 := by decide
theorem actual_reverse_one : etag (early oneS oneT)=4 := by decide
theorem actual_forward_high : etag (early highT highS)=5 := by decide
theorem actual_reverse_high : etag (early highT reverseHighS)=6 := by decide
theorem reverse_sameq_decrease :
 (leaves (contract 4 5 (commonFresh graftS) graftS)).length<(leaves graftT).length := by decide
theorem cutoff_strict : cutoff (fun _ _ _ => some [[0]]) 3 (.leaf 0) (.leaf 0) 3=none := by decide
theorem cutoff_paid : cutoff (fun _ _ _ => some [[0]]) 3 (.leaf 0) (.leaf 0) 2=some [[0]] := by decide
end OrdinaryDispatch.FastOrdinary.Controls
