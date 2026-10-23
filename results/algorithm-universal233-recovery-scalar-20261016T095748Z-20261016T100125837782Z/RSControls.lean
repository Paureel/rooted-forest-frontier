import RSCopyBounds
namespace OrdinaryDispatch.RecoveryScalar.Controls
open OrdinaryDispatch.RecoveryBits
open Universal233 CoreProgram

def zero : List Bool:=[]
def one : List Bool:=[true]
def two : List Bool:=[false,true]
def three : List Bool:=[true,true]
def five : List Bool:=[true,false,true]
def seven : List Bool:=[true,true,true]
def eight : List Bool:=[false,false,false,true]
def thousand : List Bool:=[false,false,false,true,false,true,true,true,true,true]
def blocks : List (List (List Bool)) := [[zero],[one,two]]
def g7 : BitGroup:=⟨[false],[seven],seven⟩
def out : BitOutput:=⟨[[one],[two,five]],[[false],[true,false]]⟩
def srcFour : GTree:=.node []
 (.node [false] (.leaf ⟨[false,false],[0],0⟩) (.leaf ⟨[false,true],[1],1⟩))
 (.node [true] (.leaf ⟨[true,false],[2],0⟩) (.leaf ⟨[true,true],[3],1⟩))

def checks : List (String×Bool) := [
 ("equal",(copiedEqual five five).value),
 ("order",!(leBits five three).value),
 ("minimum",(minBits five three).value==three),
 ("subtract_sat",(subtractBits three five).value==[]),
 ("subtract_two",decode (subtractBits five three).value==2),
 ("increment_carry",(counterInc 4 seven).value==eight),
 ("counter_add",(counterAdd 4 three five).value==eight),
 ("overflow_guard",decode (counterInc 3 seven).value==0),
 ("copy_exact",(copyBits five).value==five && (copyBits five).work==13),
 ("length",decode (lengthBits 4 [false,true,false]).value==3),
 ("clip",decode (clipBudget 10 thousand [false,true,false]).value==2),
 ("color_head",(colorBits blocks two).value==one),
 ("color_absent",(colorBits blocks five).value==[]),
 ("group_copy",(copyGroup g7).value==g7 && (copyGroup g7).work==49),
 ("tree_copy",(copyTree (.leaf g7)).value==.leaf g7),
 ("output_copy",(copyOutput out).value==out),
 ("all_prefixes",[0,1,2].map (fun q=>OrdinaryDispatch.RecoveryScalar.eventSize (run q srcFour [] []))==[5,9,11])]
#eval checks
example : checks.all Prod.snd=true := by decide +kernel
#eval ("PASS_RECOVERY_FINITE_CONTROLS",checks.length,checks.all Prod.snd)
end OrdinaryDispatch.RecoveryScalar.Controls
