import RecursiveConsumers
import FinalControls
namespace Universal233.Rule5SourceOrientation.Controls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Local.Pre Rule5Classification Rule5Classification.Controls Rule5FinalClassification Rule5FinalClassification.Controls
set_option maxRecDepth 10000

def firstD : BadSelection := ⟨[false,false,false,true],[false,false,true],2⟩
def thirdD : BadSelection := ⟨[false,false,true],[false,true],2⟩
example : firstChildren firstS 0 1 firstD=[singletonChild firstS 0,pendantChild firstS 0 1] := by decide
example : thirdChildren thirdS 0 1 thirdD=[singletonChild thirdS 1,pendantChild thirdS 0 1] := by decide
example : firstChildren firstS 1 0 firstD=[singletonChild firstS 0,pendantChild firstS 1 0] := by decide
example : thirdChildren thirdS 1 0 thirdD=[singletonChild thirdS 1,pendantChild thirdS 1 0] := by decide
example : siblingEndpoint? (mirror firstS) (firstD.badArc.map Bool.not)=some 0 := by decide
example : siblingEndpoint? (mirror thirdS) (thirdD.badArc.map Bool.not)=some 0 := by decide
example : (firstChildren firstS 0 1 firstD).map Child.paid=[1,2] := by decide
example : (thirdChildren thirdS 0 1 thirdD).map Child.paid=[1,2] := by decide

def tiny (s t r : Bool) : Tree := fork r (fork t (fork s (.leaf 0) (.node (.leaf 3) (.leaf 4))) (.leaf 2)) (.leaf 1)
example : [false,true].all (fun s => [false,true].all (fun t => [false,true].all
 (fun r => siblingEndpoint? (tiny s t r) [r,t,!s] == some 0)))=true := by decide
example {F : List (List Nat)} (ha : agreement firstT firstS F=true) :
 ∃c,c∈firstChildren firstS 0 1 firstD ∧ ∃G,feasible firstT firstS c G ∧ G.length≤F.length :=
 selected_first_cover first_actual first_admitted first_final ha
example {F : List (List Nat)} (ha : agreement thirdT thirdS F=true) :
 ∃c,c∈thirdChildren thirdS 0 1 thirdD ∧ ∃G,feasible thirdT thirdS c G ∧ G.length≤F.length :=
 selected_third_cover third_actual third_admitted third_final ha
#check first_child_solver
#check third_child_solver
#check selected_original_endpoint_cuts
#check selected_child_states
end Universal233.Rule5SourceOrientation.Controls
