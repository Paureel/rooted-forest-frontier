import RWInterface
namespace OrdinaryDispatch.RecoveryLocalWork.Controls
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def g7 : Group:=⟨[false],[7],7⟩
def g8 : Group:=⟨[true],[8],8⟩
def two : GTree:=.node [] (.leaf g7) (.leaf g8)
def same : GTree:=.node [] (.leaf g7) (.leaf ⟨[true],[8],7⟩)
def four : GTree:=.node []
 (.node [false] (.leaf ⟨[false,false],[0],0⟩) (.leaf ⟨[false,true],[1],1⟩))
 (.node [true] (.leaf ⟨[true,false],[2],0⟩) (.leaf ⟨[true,true],[3],1⟩))
def summary (r : Receipt):=(r.outputs.length,r.refusals.length,r.visited,r.childAttempts,r.pruned)
def fingerprint (r : Receipt):=(r.outputs,r.refusals,r.visited,r.childAttempts,r.pruned)
def marker (_ : GTree) (_ : List Group) (_ : List RMAF.Vertex) : Charged Receipt:=
 ⟨⟨[],["callback"],7,0,0⟩,11⟩
def paidColor (x : Nat) : Charged Nat:=⟨x,11⟩
def triS : Tree:=.node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def repeated : Tree:=.node (.leaf 7) (.leaf 7)
def choiceTag : Choice→Nat | .finish=>0 | .one _=>1 | .two _ _=>2 | .refuse _=>3

theorem tiny_groups : (meterGroups (.leaf g7)).value=[g7] ∧ (meterGroups (.leaf g7)).work=4 := by decide

theorem normalization : (meterNormalize same).value=.leaf ⟨[],[7,8],7⟩ ∧
 (meterNormalize two).value=two := by decide

theorem erase_cases :
 (meterErase [] two).value=none ∧ (meterErase [false] (.leaf g7)).value=none ∧
 (meterErase [false] two).value=some (.leaf g8) ∧
 (meterErase [true,true] two).value=some two := by decide

theorem known_pruned :
 [summary (meterRun 0 two [] []).value,summary (meterRun 1 two [] []).value]=
 [(0,0,1,1,1),(1,0,2,1,0)] ∧
 [summary (meterRun 0 four [] []).value,summary (meterRun 1 four [] []).value,summary (meterRun 2 four [] []).value]=
 [(0,0,1,2,2),(0,0,3,4,2),(2,0,5,4,0)] := by decide

theorem coloring_known : (meterBuild paidColor [] (.leaf 7)).coloring=11 ∧
 (meterBuild paidColor [] (.leaf 7)).work=19 ∧
 (meterInitial paidColor 1000 repeated).coloring=0 ∧
 (meterColor [] 7).value=0 ∧ (meterColor [] 7).work=2 := by decide

def runtimeChecks : List (String×Bool):=
 [("unique_priority",choiceTag (meterChoose two).value==1),
  ("uniform_priority",choiceTag (meterChoose same).value==0),
  ("two_priority",choiceTag (meterChoose four).value==2),
  ("mixed_first",(meterMixed two).value==some (g7,g8)),
  ("root_refusal",(meterAttempt marker two [] [] ⟨[],[9],9⟩).value.refusals==["attempt to cut original root"]),
  ("duplicate_refusal",(meterAttempt marker two [] [[false]] g7).value.refusals==["duplicate original source cut"]),
  ("entire_refusal",(meterAttempt marker (.leaf g7) [] [] g7).value.refusals==["attempt removed entire current source"]),
  ("one_continuation",summary (meterAttempt marker two [] [] g7).value==(0,1,7,1,0)),
  ("literal_receipts",([0,1,2].all fun q=>fingerprint (meterRun q four [] []).value==fingerprint (CoreProgram.run q four [] []))),
  ("singleton_generate",summary (meterGenerate (.leaf 7) paidColor 0).value==(1,0,1,0,0)),
  ("large_budget_generate",summary (meterGenerate (.leaf 7) paidColor 1000).value==(1,0,1,0,0)),
  ("duplicate_generate",summary (meterGenerate repeated paidColor 1000).value==(0,1,0,0,0)),
  ("recovery_singleton",(meterRecover (.leaf 7) [[7]]).value==some ⟨[[7]],[]⟩),
  ("recovery_two",(meterRecover triS [[0],[1,2]]).value==some ⟨[[0],[1,2]],[[false]]⟩),
  ("recovery_refused",(meterRecover triS [[0],[1],[1]]).value.isNone)]
#eval ("PRUNED_KNOWN",[0,1,2].map (fun q=>summary (meterRun q four [] []).value))
#eval ("COLOR_KNOWN",(meterBuild paidColor [] (.leaf 7)).coloring,(meterBuild paidColor [] (.leaf 7)).work,(meterInitial paidColor 1000 repeated).coloring)
#eval runtimeChecks
#eval ("PASS_RECOVERY_SOURCE_CONTROLS",runtimeChecks.length,runtimeChecks.all Prod.snd)
#eval ("SOURCE_WORK",(meterRun 0 four [] []).work,(meterRun 1 four [] []).work,(meterRun 2 four [] []).work,
 (meterRecover (.leaf 7) [[7]]).work,(meterRecover triS [[0],[1,2]]).work)
end OrdinaryDispatch.RecoveryLocalWork.Controls
