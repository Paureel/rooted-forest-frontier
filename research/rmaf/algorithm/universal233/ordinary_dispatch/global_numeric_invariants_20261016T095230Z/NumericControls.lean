import NumericInterface
namespace OrdinaryDispatch.GlobalNumeric.Controls
open RMAF ForestState Universal233 Universal233.CherryBranching Universal233.BothBad
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FastOrdinary

def failed : Nat→Tree→Tree→Option CommonForest := fun _ _ _=>none
def four (a b c d : Nat) : Tree := .node (.node (.leaf a) (.leaf b)) (.node (.leaf c) (.leaf d))
def baseT : Tree := .node (four 0 1 2 3) (.leaf 4)
def baseS : Tree := .node (four 0 2 1 3) (.leaf 4)
def T : Tree := .node baseT (.node (.leaf 5) (.leaf 6))
def S : Tree := .node baseS (.node (.leaf 5) (.leaf 6))

theorem literal_fresh : commonFresh (.node (.leaf 3) (.leaf 9))=10 ∧
 ForestState.contract 3 9 10 (.node (.leaf 9) (.leaf 3))=.leaf 10 := by decide

theorem budget_above_reduced_size : DepthOne.proper (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))=true ∧
 Reach failed 8 (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) 0 (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) 8 ∧
 (leaves (.node (.leaf 0) (.leaf 1))).length<8 := ⟨by decide,.root,by decide⟩

theorem common_zero : DepthOne.proper T S=true ∧
 ((ordinaryStepTrace failed 0 T S).queries.map fun x=>(x.2,(leaves x.1.1).length))=[(0,6)] ∧
 ((ordinaryStepTrace failed 0 S T).queries.map fun x=>(x.2,(leaves x.1.1).length))=[(0,6)] := by decide

def repeated : List Call := [⟨some baseT,[baseS],2⟩,⟨some baseT,[baseS],2⟩]
theorem duplicate_failed : (forestQueries (fun _ _ _=>none) repeated).length=2 := by
 have active : proper (some baseT) [baseS]=true ∧ agrees (some baseT) [baseS] [leaves baseS]=false := by decide
 have one : frontier (fun _ _ _=>none) (some baseT) [baseS] 2=[((baseT,baseS),2)] := by
  rw [frontier.eq_def]
  simp only [List.map_cons,List.map_nil,active.1,active.2,Bool.not_false,Bool.and_self,ite_true]
 simp only [forestQueries,repeated,List.flatMap_cons,List.flatMap_nil,one]
 rfl

theorem refused_empty : (ordinaryStepTrace failed 8 (.leaf 0) (.leaf 1)).queries=[] ∧
 ordinaryForestCalls failed 8 (.leaf 0) (.leaf 1)=[] := by decide

theorem empty_forest : GenericForest.targetNodes none=0 ∧ GenericForest.sourceNodes []=0 ∧
 proper none []=true := by decide

theorem zero_budget_width : GenericForest.CheckCorrespondence.labelBits (0-1)=1 := by decide

theorem padding_unbounded (W : Nat) : (List.replicate (W+1) false).length>W := by simp
end OrdinaryDispatch.GlobalNumeric.Controls
