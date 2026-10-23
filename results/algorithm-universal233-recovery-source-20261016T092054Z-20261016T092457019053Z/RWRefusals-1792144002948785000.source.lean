import RWInterface
namespace OrdinaryDispatch.RecoveryLocalWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.OptimizerLocalWork

/-- Refused final inputs use literal raw block/cell sizes, never accepted-payload
bounds, and incur no generator or coloring call. -/
theorem final_source_refused (S : Tree) (P : CommonForest) (N : Nat)
 (refused : FinalCutRecovery.inputCheck S P=false)
 (sn : treeNodes S≤N) (blocks : P.length≤N) (cells : P.flatten.length≤N) :
 (meterRecover S P).value=none ∧ (meterRecover S P).work≤2048*(N+1)^5+8 := by
 have guard:=meterInputCheck_bound S P N sn blocks cells
 simp only [meterRecover,meterInputCheck_value,refused,ite_false]
 exact ⟨rfl,Nat.add_le_add_right guard 8⟩

/-- Duplicate original labels refuse before fromTree/coloring and before run. -/
theorem generate_source_refused (t : Tree) (color : Nat→Charged Nat) (budget : Nat)
 (duplicate : ¬(leaves t).Nodup) :
 (meterGenerate t color budget).value=⟨[],["duplicate original label"],0,0,0⟩ ∧
 (meterInitial color budget t).coloring=0 ∧
 (meterGenerate t color budget).work≤initialCharge t+8 := by
 have initial:=meterInitial_bound color budget t
 have coloring:=meterInitial_coloring color budget t
 simp only [duplicate,ite_false] at coloring
 simp only [meterGenerate,meterInitial_value,duplicate,ite_false]
 refine ⟨rfl,coloring,?_⟩
 omega
end OrdinaryDispatch.RecoveryLocalWork
