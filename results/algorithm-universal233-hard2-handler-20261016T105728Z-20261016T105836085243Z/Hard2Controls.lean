import Hard2Exact
import PairControls
namespace OrdinaryDispatch.Hard2Dispatcher.Controls
open RMAF Universal233 Universal233.CherryBranching Universal233.Hard2Overlap

def four (a b c d : Nat) : Tree := .node (.node (.leaf a) (.leaf b)) (.node (.leaf c) (.leaf d))
def T : Tree := .node (four 0 1 2 3) (.leaf 4)
def S : Tree := .node (four 0 2 1 3) (.leaf 4)
def c : Candidate := ⟨[false,false],0,1,[[false,false,true],[false,true,true]]⟩
def d : Candidate := ⟨[false,false],0,2,[[false,false,true],[false,true,true]]⟩
def refusal : Ordinary := fun _ _ _=>none

theorem direct_literal : DepthOne.proper T S=true ∧ DepthOne.pretest01 T S=.rejected ∧
 CherryBranching.select T S=some (.hard2,c) ∧ runHard2 T S c=some .disjoint ∧
 (pendantPartition S c.a c.b).all (restrictionAgrees T S)=true := by decide

theorem whole_direct_answer : (run refusal T S c d 2).any
 (fun F=>agreement T S F && decide (F.length=3))=true ∧ run refusal T S c d 1=none := by cbv

namespace PairRoute
open OrdinaryDispatch.GoodPairDP.Controls

def raw : Candidate := ⟨[false,false],0,1,[[false,false],[false,true]]⟩
def edge : RMAF.Vertex×RMAF.Vertex := ([false],[false,false])

theorem actual_raw_graph : runHard2 target (source badC) raw=some (.pair .abc (.edge edge)) := by decide

theorem actual_whole_pair_routing :
 ((paidCase depthAnswer target (source badC) raw 4 (.pair .abc (.edge edge))).calls.map BothBad.Call.budget)=[1] ∧
 (paidCase depthAnswer target (source badC) raw 4 (.pair .abc (.edge edge))).answer.any
 (fun F=>agreement target (source badC) F && decide (F.length-1≤4))=true := by cbv
end PairRoute

namespace ActualFirst
open Rule5Local.Pre

def c : Candidate := ⟨[false,false,false,false,true],3,4,[[false,false,true,false,false,true],[false,false,true,false,true]]⟩
def d : Candidate := ⟨[false,false,true,false,false,true,true],7,8,[[false,false,false,false],[false,false,true]]⟩
def hostile : Ordinary := fun _ _ _=>some [[999]]

theorem priority_and_graph : DepthOne.proper commonT commonS=true ∧
 CherryBranching.select commonT commonS=some (.hard2,c) ∧
 CherryBranching.select commonS commonT=some (.hard2,d) ∧
 Rule4.select commonT commonS=none ∧ Rule4.select commonS commonT=none ∧
 DepthOne.pretest01 commonT commonS=.rejected ∧
 Rule5Local.admitted commonT commonS c.a c.b=false ∧
 runHard2 commonT commonS c=some (.pair .acb (.vertex [false,false,false])) := by decide

theorem no_zero_budget_fabrication : run hostile commonT commonS c d 0=none := by cbv
end ActualFirst
end OrdinaryDispatch.Hard2Dispatcher.Controls
