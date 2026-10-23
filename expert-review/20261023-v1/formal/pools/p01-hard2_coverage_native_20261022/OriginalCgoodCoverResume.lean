import ControlFlowV4
import ActualCgoodCover
import ActualExecutionAliasesNative
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
set_option autoImplicit false
namespace ContactedHard2Survival

theorem original_paid_instance_binding (q : Nat) :
 PaidInstances.OwnPaid OrdinaryDispatch.FastOrdinary.solve q=IndependentReconstruction.OwnPaid q := by
 funext u v r
 unfold PaidInstances.OwnPaid IndependentReconstruction.OwnPaid
 split <;>rfl

theorem original_parent_execution_contract (q : Nat) (below : IndependentReconstruction.BelowBudget q) :
 ParentExecutionContract (GenericForest.solve (IndependentReconstruction.OwnPaid q)) q := by
 intro T S P b proper partS embS partT embT strict F agree ref budget
 have pp:=IndependentReconstruction.proper_parts proper
 have actual:=(ActualOrdinaryExecution.contract q b below strict T S P pp.1 pp.2.1 partT partS embT embS).1
 cases result : (BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid q)) T S P b).answer with
 | none=>
  rw [result] at actual
  have impossible:=actual F agree ref
  omega
 | some G=>
  rw [result] at actual
  exact ⟨G,rfl,actual.1,actual.2.2.2 F agree ref⟩

theorem original_actual_bothbad_cgood_cover (q : Nat) (T S : Tree)
 (c d : Candidate) (p r : RMAF.Vertex) (ord : ContactedHard2Overlap.Order) (e : RMAF.Vertex×RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (selected : OrdinaryDispatch.FastOrdinary.early T S=.hard2 c d) (shape : c.originalCuts=[p,r])
 (picked : Hard2Overlap.runHard2 T S c=some (ContactedHard2Survival.originalResult (.pair ord (.edge e))))
 (below : IndependentReconstruction.BelowBudget q)
 (badA : restrictionAgrees S T (ContactedHard2Overlap.first ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r))=false)
 (badB : restrictionAgrees S T (ContactedHard2Overlap.second ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r))=false)
 (goodC : restrictionAgrees S T (ContactedHard2Overlap.third ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r))=true)
 (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(BothBad.solvePair (GenericForest.solve (IndependentReconstruction.OwnPaid q)) S T
  (ContactedHard2Overlap.first ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r))
  (ContactedHard2Overlap.second ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r))
  (ContactedHard2Overlap.third ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r)) e q).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 have parametricBelow : PaidInstances.BelowBudget OrdinaryDispatch.FastOrdinary.solve q:=below
 have contract : ParentExecutionContract (GenericForest.solve (PaidInstances.OwnPaid OrdinaryDispatch.FastOrdinary.solve q)) q:=by
  rw [original_paid_instance_binding q]
  exact original_parent_execution_contract q below
 have covered:=actual_bothbad_cgood_cover OrdinaryDispatch.FastOrdinary.solve q T S c d p r ord e
  proper selected shape picked parametricBelow contract badA badB goodC F agree together budget
 simpa only [original_paid_instance_binding q] using covered
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.original_paid_instance_binding
#print axioms ContactedHard2Survival.original_paid_instance_binding
#check @ContactedHard2Survival.original_parent_execution_contract
#print axioms ContactedHard2Survival.original_parent_execution_contract
#check @ContactedHard2Survival.original_actual_bothbad_cgood_cover
#print axioms ContactedHard2Survival.original_actual_bothbad_cgood_cover
