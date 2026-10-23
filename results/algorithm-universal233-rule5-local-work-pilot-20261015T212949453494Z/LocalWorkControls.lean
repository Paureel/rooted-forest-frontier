import CandidateNumeric
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source

def enumControl (FM FN : Forest) : Bool :=
 let r:=mergeMeter [0,1] [2,3] 0 2 4 5 FM FN
 let N:=cells FM+cells FN+4
 decide (r.value=mergeCandidates [0,1] [2,3] 0 2 4 5 FM FN) &&
 decide (r.value.length=FM.length*FN.length) &&
 decide (r.work≤4*N+((8*(N+2)^2+2)*N+2)*N+1) &&
 r.value.all (fun G=>decide (cells G≤6*N+1))

def trueCheck (F : Forest) : Measured Bool := ⟨!F.isEmpty,7⟩
def falseCheck (_ : Forest) : Measured Bool := ⟨false,7⟩
def alwaysCheck (_ : Forest) : Measured Bool := ⟨true,7⟩
def controls : List (String×Bool) :=
 [("empty",enumControl [] [[2]]),
  ("singleton",enumControl [[0,1]] [[2,3]]),
  ("duplicate_owners",enumControl [[0],[0],[1]] [[2],[3]]),
  ("best_early_valid",(bestMeter trueCheck [[[0]],[]]).value==some [[0]]),
  ("best_late_valid",(bestMeter trueCheck [[],[[0]]]).value==some [[0]]),
  ("best_all_invalid",(bestMeter falseCheck [[],[[0]],[]]).value==none),
  ("invalid_checks_paid",decide ((bestMeter falseCheck [[],[[0]],[]]).work=36)),
  ("valid_checks_paid",decide ((bestMeter alwaysCheck [[],[[0]],[]]).work=36)),
  ("missing_owner_same_answer",let cs:=(mergeMeter [0] [2] 0 2 4 5 [[0],[0]] [[2],[2]]).value
    (bestMeter alwaysCheck cs).value==(bestMeter alwaysCheck cs.tail).value &&
    decide (cs.length=4) && decide (cs.tail.length≠4)),
  ("fresh_build",let T:=Tree.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
    match buildSetup T T [0,1] [2,3] [false] with
    | none=>false
    | some d=>decide (d.rho=4 ∧ d.gamma=5)),
  ("malformed_build",(buildSetup (.leaf 0) (.leaf 0) [] [] []).isNone),
  ("closed_actual_payload",let T:=Tree.node (.leaf 0) (.leaf 1)
    match actual T T 0 with
    | none=>false
    | some F=>decide (F.flatten.length=2 ∧ cells F≤4))]
#eval controls
#eval ("PASS_LITERAL_LOCAL_WORK_CONTROLS",controls.all Prod.snd)
end Universal233.Rule5LocalWork
