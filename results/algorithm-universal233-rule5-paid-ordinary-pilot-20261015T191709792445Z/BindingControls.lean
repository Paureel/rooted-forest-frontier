import SelectedExact
import SelectorControls
import ForestPretestControls
namespace Universal233.Rule5PaidOrdinary.Controls
open RMAF ForestState Rule5PaidSelector Rule5Case322 Rule5Local Rule5Local.Pre
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000

def emptyActual : Ordinary := fun _ _ _ => none
abbrev ft := ForestPretest01.Controls.t
abbrev fss := ForestPretest01.Controls.ss
abbrev fw := ForestPretest01.Controls.witness
example : currentQuery emptyActual none [] 0=.answered (some []) := by decide
example : currentQuery emptyActual (some (.leaf 9)) [.leaf 9] 0=.answered (some [[9]]) := by decide
example : currentQuery emptyActual (some ft) fss 0=.answered none := by decide
example : currentQuery emptyActual (some ft) fss 1=.answered (some fw) := by decide
example : currentQuery emptyActual none [.leaf 9] 0=.malformed := by decide
example : currentQuery emptyActual (some ForestPretest01.Controls.rejectT) ForestPretest01.Controls.rejectSS 1=.answered none := by decide
example : currentQuery emptyActual (some ForestPretest01.Controls.rejectT) ForestPretest01.Controls.rejectSS 2=
 .answered (GenericForest.solve emptyActual (some ForestPretest01.Controls.rejectT) ForestPretest01.Controls.rejectSS 2) := by
 have hp : ForestPretest01.pretest01 (some ForestPretest01.Controls.rejectT) ForestPretest01.Controls.rejectSS=.rejected := by decide
 simp [currentQuery,hp]
example : solveSelected emptyActual sixT sixS 0 1 0=.answered none := by decide

def hasAnswer : SelectedResult → Bool
 | .builderRefused => false
 | .answered F => F.isSome
def knownF : Forest := [[14],[15,16],[2],[0,1]]
example : agreement sixT sixS knownF=true ∧ knownF.length-1=3 := by decide

def actualR : SelectedPaid sixT sixS := (buildSelected sixT sixS 0 1).get (by decide)
theorem actualR_built : buildSelected sixT sixS 0 1=some actualR := (Option.some_get (o := buildSelected sixT sixS 0 1) (by decide)).symm
def actualQ : PaidRequest := ⟨hardBranch sixS 0 1,sixT,Rule5Case322.sourceForest sixT sixS (hardBranch sixS 0 1),1⟩
theorem actualQ_mem : actualQ∈requests actualR.geometry 3 := by decide
theorem actualQ_answer : currentAnswer emptyActual (some actualQ.target) actualQ.sources actualQ.residual=some knownF := by decide
example : hasAnswer (solveSelected emptyActual sixT sixS 0 1 3)=true := by
 have hm : knownF∈answers emptyActual actualR 3 := List.mem_filterMap.2 ⟨actualQ,actualQ_mem,actualQ_answer⟩
 have accepted : originalAccepted sixT sixS 3 knownF=true := by decide
 obtain ⟨F,hF⟩ := best_exists List.length (originalAccepted sixT sixS 3) (answers emptyActual actualR 3) knownF hm accepted
 simp [solveSelected,actualR_built,bestFor,hF,hasAnswer]

-- Omitting every actual paid request loses this literal feasible witness.
def missingRequests : Option Forest := best List.length (originalAccepted sixT sixS 3) []
example : missingRequests=none := by decide
-- The unit-paid child must receive zero residual at parent budget one.
example : (buildSelected sixT sixS 0 1).map (fun R => (requests R.geometry 1).map (fun Q =>
 decide (Q.residual=0) && decide (Q.branch.originalCuts.length=1) && decide (Q.sources.length=2)))=some [true] := by decide
example : solveSelected emptyActual (.leaf 9) (.leaf 9) 0 1 0=.builderRefused := by decide
end Universal233.Rule5PaidOrdinary.Controls
