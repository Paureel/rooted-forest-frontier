import OrdinaryLocal
import GoodPair
namespace Universal233.Hard2PaidLocal.Controls
open RMAF CoreProgram BothBad
set_option maxRecDepth 10000
def source : Tree := .node (.leaf 0) (.leaf 1)
def source3 : Tree := .node source (.leaf 2)
def cut : Output := ⟨[[0],[1]],[[false]]⟩
def zero : Output := ⟨[[0,1]],[]⟩
def noOrd (_ _ : Tree) (_ : Nat) : Option Forest := none
def literalRun (q : Nat) (outputs : List Output) : Execution :=
 execute (GenericForest.solve noOrd) source source q (entries q .full outputs)
theorem cut_call : ((literalRun 1 [cut]).calls.map Call.budget)=[0] := by
 simp only [literalRun,execute,entries,List.filterMap_cons,List.filterMap_nil,cut,Mode.extra]
 decide
theorem cut_sources : ((literalRun 1 [cut]).calls.map Call.sources)=[[.leaf 0,.leaf 1]] := by decide
theorem unaffordable_no_call : (literalRun 0 [cut]).calls=[] ∧ (literalRun 0 [cut]).answer=none := by decide
theorem duplicate_occurrences : ((literalRun 1 [cut,cut]).calls.map Call.budget)=[0,0] := by decide
theorem zero_boundary_same_budget : ((literalRun 1 [zero]).calls.map Call.budget)=[1] := by decide
theorem original_check : checked source source 1 (some [[999]])=none := by decide
theorem three_parent_generation :
 (WholeSourceMass.wholeOutputs source3 [0] [1] (fun _=>0) (fun _=>0) (fun _=>0) 2).isEmpty=false ∧
 (WholeSourceMass.wholeOutputs source3 [0] [1] (fun _=>0) (fun _=>0) (fun _=>0) 2).all (fun o=>o.sourceCuts.length==2)=true := by decide
end Universal233.Hard2PaidLocal.Controls
