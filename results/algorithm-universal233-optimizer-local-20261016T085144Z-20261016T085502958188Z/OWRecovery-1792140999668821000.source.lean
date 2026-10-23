import OWScan
namespace OrdinaryDispatch.OptimizerLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.BudgetOptimization

/-- Raw guard meter, including refused partitions and repeated leaf lists. -/
def meterInputCheck (S : Tree) (P : CommonForest) : Charged Bool :=
 let a:=meterLeaves S;let n:=meterNodup a.value
 let b:=meterLeaves S;let p:=meterPartition b.value P
 let e:=meterPairwise S P
 ⟨n.value&&p.value&&e.value,a.work+n.work+b.work+p.work+e.work+8⟩
@[simp] theorem meterInputCheck_value (S P) : (meterInputCheck S P).value=FinalCutRecovery.inputCheck S P := by
 simp [meterInputCheck,FinalCutRecovery.inputCheck]

theorem meterInputCheck_bound (S : Tree) (P : CommonForest) (N : Nat)
 (sn : treeNodes S≤N) (blocks : P.length≤N) (cells : P.flatten.length≤N) :
 (meterInputCheck S P).work≤2048*(N+1)^5 := by
 have leaflen:=Nat.le_trans (leaves_nodes S) sn
 have a:=cap_lift N 8 2 5 _ (meterLeaves_cap S N sn) (by decide)
 have n:=Nat.le_trans (meterNodup_bound (leaves S))
  (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right leaflen 1) 2))
 have nn:=cap_lift N 8 2 5 _ n (by decide)
 have p:=cap_lift N 128 2 5 _ (meterPartition_bound (leaves S) P N leaflen blocks cells) (by decide)
 have e:=meterPairwise_polynomial S P N sn leaflen blocks
  (fun B hb=>Nat.le_trans (block_cells P B hb) cells)
 have pos : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 simp only [meterInputCheck,meterLeaves_value];omega

/-- The old guard coefficient covers this derived raw guard plus literal
P.length, subtraction/head/control slots. It is not used to prove the guard. -/
theorem recovery_guard_covered (S : Tree) (P : CommonForest) :
 (meterInputCheck S P).work+(meterLength P).work+4≤FinalCutRecovery.guardCharge S P := by
 let N:=treeNodes S+P.flatten.length+P.length
 have m:=meterInputCheck_bound S P N (by simp only [N];omega) (by simp only [N];omega) (by simp only [N];omega)
 have lift:=cap_lift N 2048 5 8 _ m (by decide)
 have len:=meterLength_work P
 have small : P.length+1≤(N+1)^8:=Nat.le_trans (by simp only [N];omega) (by simpa using pow_mono N 1 8 (by decide))
 have pos : 1≤(N+1)^8:=Nat.one_le_pow _ _ (by omega)
 have bound : (meterInputCheck S P).work+(meterLength P).work+4≤4096*(N+1)^8:=by omega
 have scale:=Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left (show N+1≤treeNodes S+P.flatten.length+P.length+2 by simp only [N];omega) 8)
 exact Nat.le_trans bound scale

/-- Complete raw recovery wrapper around the unchanged meterGenerate provider.
The provider's receipt is exact; its initial/local charge interpretation remains
an explicit open source obligation, not a claim of this definition. -/
def meterRecovery (S : Tree) (P : CommonForest) : Charged (Option CoreProgram.Output) :=
 let check:=meterInputCheck S P
 if check.value then
  let n:=meterLength P
  let g:=CoreWork.meterGenerate S (FinalCutRecovery.blockColor P) (n.value-1)
  let colors:=((leaves S).map (fun x=>(FinalCutRecovery.meterColor P x).work)).sum
  ⟨g.measured.receipt.outputs.head?,check.work+g.measured.work+colors+n.work+4⟩
 else ⟨none,check.work+2⟩
@[simp] theorem meterRecovery_value (S P) : (meterRecovery S P).value=FinalCutRecovery.recover S P := by
 simp only [meterRecovery,meterInputCheck_value,meterLength_value,CoreWork.meterGenerate_receipt,FinalCutRecovery.recover]
 split <;> rfl

theorem meterRecovery_le_legacy (S : Tree) (P : CommonForest) :
 (meterRecovery S P).work≤(FinalCutRecovery.meterRecover S P).work := by
 have check:=recovery_guard_covered S P
 have colors:=FinalCutRecovery.total_color_work P (leaves S)
 simp only [meterRecovery,meterInputCheck_value,meterLength_value,FinalCutRecovery.meterRecover]
 split <;> simp only [Charged.work,FinalCutRecovery.RecoveryMeasured.work]
 · dsimp only [FinalCutRecovery.colorCharge];omega
 · omega

/-- Legacy generator counter envelope, explicitly retaining its source-provider
qualification. No proof here interprets CoreWork.initialCharge/localCharge. -/
theorem recovery_counter_bound (S : Tree) (P : CommonForest)
 (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true)
 (he : pairwiseEmbeddings S P=true) :
 (meterRecovery S P).work≤FinalCutRecovery.finalPolynomial S P*2^(P.length-1) :=
 Nat.le_trans (meterRecovery_le_legacy S P) (FinalCutRecovery.final_work_bound S P hn hp he)
end OrdinaryDispatch.OptimizerLocalWork
