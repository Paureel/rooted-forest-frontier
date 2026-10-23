import MafCaller

namespace Universal233.MafScheduler.Precontrols
open RMAF
def four (i : Nat) : Tree := .node (.node (.leaf i) (.leaf (i+1))) (.node (.leaf (i+2)) (.leaf (i+3)))
def cross (i : Nat) : Tree := .node (.node (.leaf i) (.leaf (i+2))) (.node (.leaf (i+1)) (.leaf (i+3)))
def comb (i : Nat) : Tree := .node (.node (.leaf i) (.node (.leaf (i+1)) (.leaf (i+2)))) (.leaf (i+3))
def group (i : Nat) : List Nat := [i,i+1,i+2,i+3]
def three (i : Nat) : Forest := [[i],[i+1],[i+2,i+3]]
-- Explicit planted recursive table, agreement-guarded; never claimed complete.
def table (t s : Tree) (b : Nat) : Option Forest :=
  let F := three (leaves s).head!
  if agreement t s F && decide (F.length-1 ≤ b) then some F else none

theorem control_good_zero : solveDisjoint (four 0) (four 0) table 0 [group 0]=some [group 0] ∧
    calls (four 0) (four 0) table 0 [group 0]=[] := by decide
theorem control_one : (solveDisjoint (four 0) (comb 0) table 1 [group 0]).isSome=true ∧
    calls (four 0) (comb 0) table 1 [group 0]=[] := by decide
theorem control_hard_locals : DepthOne.pretest01 (cross 0) (four 0)=.rejected ∧
    agreement (cross 0) (four 0) (three 0)=true := by decide
theorem control_two_hard :
    solveDisjoint (.node (cross 0) (cross 4)) (.node (four 0) (four 4)) table 4 [group 0,group 4]=
      some (three 0++three 4) ∧
    calls (.node (cross 0) (cross 4)) (.node (four 0) (four 4)) table 4 [group 0,group 4]=[2,2] := by decide
theorem control_prune_two :
    solveDisjoint (.node (cross 0) (cross 4)) (.node (four 0) (four 4)) table 3 [group 0,group 4]=none ∧
    calls (.node (cross 0) (cross 4)) (.node (four 0) (four 4)) table 3 [group 0,group 4]=[] := by decide
theorem control_one_and_hard :
    (solveDisjoint (.node (four 0) (cross 4)) (.node (comb 0) (four 4)) table 3 [group 0,group 4]).isSome=true ∧
    calls (.node (four 0) (cross 4)) (.node (comb 0) (four 4)) table 3 [group 0,group 4]=[2] := by decide
theorem control_order :
    solveDisjoint (.node (cross 0) (cross 4)) (.node (four 0) (four 4)) table 4 [group 4,group 0]=
      some (three 4++three 0) := by decide
theorem control_global_witness :
    agreement (.node (cross 0) (cross 4)) (.node (four 0) (four 4)) (three 0++three 4)=true ∧
    (three 0++three 4).length-[group 0,group 4].length=4 := by decide
theorem control_overlap_guard :
    pairwiseEmbeddings (four 0) [[0,2],[1,3]]=false ∧
    agreement (four 0) (cross 0) [[0,2],[1,3]]=false := by decide
theorem control_refusal : prepare (four 0) (four 0) [[0,1,2,99]]=none := by decide
end Universal233.MafScheduler.Precontrols
