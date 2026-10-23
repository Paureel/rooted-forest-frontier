/- Definition-only fixtures fixed before forward Rule4 mathematics. -/
import ChoiceElimination
open RMAF ForestState OutputState Universal233 OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace ContactedForward

def fixtureT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def fixtureS : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def raw : Rule4.RawChoice := ⟨0,1,2,[false,true],[true,true]⟩
def choice : Rule4.Choice fixtureT fixtureS := ⟨raw,by decide,by decide⟩

def payments (q : Nat) := (Rule4.branches choice).map (fun b =>
 (b.cost,if b.cost≤q then some (q-b.cost) else none))

theorem positive_domain_control :
 DepthOne.proper fixtureT fixtureS=true ∧ DepthOne.pretest01 fixtureT fixtureS=.rejected ∧
 early fixtureT fixtureS=.rule4Forward choice := by exact ⟨by decide,rfl,rfl⟩

theorem actual_branch_control :
 (Rule4.branches choice).map Rule4.Branch.cost=[2,1,2] ∧
 (Rule4.branches choice).map Rule4.Branch.partition=
 [[[2],[3],[0,1]],[[0],[2,1,3]],[[1],[3],[0,2]]] ∧
 ((Rule4.branches choice).all (fun b=>partitionCheck (leaves b.source) b.partition))=true ∧
 ((Rule4.branches choice).all (fun b=>pairwiseEmbeddings b.source b.partition))=true := by decide

theorem affordability_control :
 payments 0=[(2,none),(1,none),(2,none)] ∧
 payments 1=[(2,none),(1,some 0),(2,none)] ∧
 payments 2=[(2,some 0),(1,some 1),(2,some 0)] := by decide

theorem forged_guard_control :
 ¬Rule4.LocalGuard fixtureT fixtureS (Rule4.RawChoice.mk 0 1 2 [true,true] [false,true]) := by decide

theorem unaffordable_hostile_control :
 Rule4.outputs choice 0 (fun _ _=>some [[99]])=[] := by decide

theorem callback_premise_essential_control :
 Rule4.solveForest choice 1 (fun _ _=>some [])=some [] ∧
 agreement fixtureT fixtureS []=false := by decide

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.positive_domain_control
#print axioms ContactedForward.positive_domain_control
#check @ContactedForward.actual_branch_control
#print axioms ContactedForward.actual_branch_control
#check @ContactedForward.affordability_control
#print axioms ContactedForward.affordability_control
#check @ContactedForward.forged_guard_control
#print axioms ContactedForward.forged_guard_control
#check @ContactedForward.unaffordable_hostile_control
#print axioms ContactedForward.unaffordable_hostile_control
#check @ContactedForward.callback_premise_essential_control
#print axioms ContactedForward.callback_premise_essential_control
