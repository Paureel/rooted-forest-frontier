import RWInitial
namespace OrdinaryDispatch.RecoveryLocalWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.OptimizerLocalWork OrdinaryDispatch.BudgetOptimization

/-- Actual block contains/early-stop/headD scan; scalar label comparisons use
only the completed unit comparator, not a unit whole-color oracle. -/
def meterColor : CommonForest→Nat→Charged Nat
 | [],_=>⟨0,2⟩
 | b::P,x=>let contains:=meterContains x b
   if contains.value then ⟨b.headD 0,contains.work+8⟩
   else let r:=meterColor P x;⟨r.value,contains.work+r.work+8⟩
@[simp] theorem meterColor_value (P x) : (meterColor P x).value=FinalCutRecovery.blockColor P x := by
 induction P <;> simp_all [meterColor,FinalCutRecovery.blockColor]
theorem meterColor_bound (P : CommonForest) (x : Nat) :
 (meterColor P x).work≤32*(P.flatten.length+P.length+1) := by
 induction P with
 | nil=>simp [meterColor]
 | cons b P ih=>
  have contains:=meterContains_bound x b
  simp only [meterColor,List.flatten_cons,List.length_append,List.length_cons]
  split <;> simp only [Charged.work] <;> omega

theorem color_sum_bound (P : CommonForest) (xs : List Nat) :
 ((xs.map (fun x=>(meterColor P x).work)).sum)≤32*xs.length*(P.flatten.length+P.length+1) := by
 induction xs with
 | nil=>simp
 | cons x xs ih=>
  have a:=meterColor_bound P x
  simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

def meterRecover (S : Tree) (P : CommonForest) : Charged (Option Output) :=
 let check:=meterInputCheck S P
 if check.value then
  let len:=meterLength P
  let g:=meterGenerate S (meterColor P) (len.value-1)
  ⟨g.value.outputs.head?,check.work+len.work+g.work+8⟩
 else ⟨none,check.work+8⟩
@[simp] theorem meterRecover_value (S P) : (meterRecover S P).value=FinalCutRecovery.recover S P := by
 simp only [meterRecover,meterInputCheck_value,meterLength_value,meterGenerate_value,meterColor_value,FinalCutRecovery.recover]
 split <;> rfl

/-- New derived polynomial coefficient, retaining every source/pruned prefix.
The exponential factor is 2^(P.length-1), never removed by final uniqueness. -/
def finalSourcePolynomial (S : Tree) (P : CommonForest) : Nat :=
 (FinalCutRecovery.guardCharge S P+FinalCutRecovery.colorCharge S P+initialCharge S+32)+
  32*(localCap (inputResource S)+6)*P.length

theorem final_source_work_bound (S : Tree) (P : CommonForest)
 (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true)
 (he : pairwiseEmbeddings S P=true) :
 (meterRecover S P).work≤finalSourcePolynomial S P*2^(P.length-1) := by
 have flat:=(FinalCutRecovery.checked_flatten_perm S P hn hp).length_eq
 have blocks:=FinalCutRecovery.blocks_le_flatten P (SourceCoverage.partitionCheck_nonempty _ _ hp)
 have positive:=RankDichotomy.inputRank_pos S (FinalCutRecovery.blockColor P)
 rw [FinalCutRecovery.checked_rank S P hp] at positive
 have clip : min (P.length-1) ((leaves S).length-1)=P.length-1:=by omega
 have plen : P.length-1+1=P.length:=by omega
 have doubling : 2^P.length=2*2^(P.length-1):=by
  calc 2^P.length=2^(P.length-1+1):=congrArg (fun n=>2^n) plen.symm
       _=2*2^(P.length-1):=by rw [Nat.pow_succ];ac_rfl
 have guard:=(FinalCutRecovery.inputCheck_iff S P).2 ⟨hn,hp,he⟩
 have check:=recovery_guard_covered S P
 have generated:=meterGenerate_bound S (meterColor P) (P.length-1)
 rw [clip,plen] at generated
 let K:=localCap (inputResource S)+6
 have factor : 16*(K*P.length*2^P.length)=(32*K*P.length)*2^(P.length-1) := by
  rw [doubling,show 32=16*2 from rfl]
  ac_rfl
 change (meterGenerate S (meterColor P) (P.length-1)).work≤initialCharge S+
  16*(K*P.length*2^P.length)+((leaves S).map (fun x=>(meterColor P x).work)).sum+8 at generated
 rw [factor] at generated
 have colors:=color_sum_bound P (leaves S)
 change ((leaves S).map (fun x=>(meterColor P x).work)).sum≤FinalCutRecovery.colorCharge S P at colors
 have pow : 1≤2^(P.length-1):=Nat.one_le_pow _ _ (by decide)
 have base:=Nat.mul_le_mul_left (FinalCutRecovery.guardCharge S P+FinalCutRecovery.colorCharge S P+initialCharge S+32) pow
 simp only [Nat.mul_one] at base
 simp only [meterRecover,meterInputCheck_value,guard,ite_true,meterLength_value]
 simp only [finalSourcePolynomial,Nat.add_mul]
 change (meterInputCheck S P).work+(meterLength P).work+(meterGenerate S (meterColor P) (P.length-1)).work+8≤_
 dsimp only [K] at generated
 omega

/-- Explicit uniform multiplier after the source proof. The old finalPolynomial
and its constants are preserved; only polynomial arithmetic is reused here. -/
theorem finalSourcePolynomial_legacy (S : Tree) (P : CommonForest) :
 finalSourcePolynomial S P≤64*(FinalCutRecovery.finalPolynomial S P+32) := by
 let A:=FinalCutRecovery.guardCharge S P+FinalCutRecovery.colorCharge S P+initialCharge S+1
 let k:=CoreWork.cap (inputResource S)
 have coefficient :32*(4*k+6)≤128*(k+6):=by omega
 have term:=Nat.mul_le_mul_right P.length coefficient
 have expanded :64*(A+2*(k+6)*P.length+32)=64*A+128*(k+6)*P.length+2048 := by
  simp only [Nat.mul_add,←Nat.mul_assoc]
 change A+31+32*(4*k+6)*P.length≤64*(A+2*(k+6)*P.length+32)
 rw [expanded]
 omega

def recoverySourceEnvelope (n : Nat) : Nat:=64*(recoveryEnvelope n+32)

theorem final_source_uniform (S : Tree) (P : CommonForest)
 (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true)
 (he : pairwiseEmbeddings S P=true) :
 (meterRecover S P).work≤recoverySourceEnvelope (leaves S).length*2^(P.length-1) := by
 have old:=Nat.le_trans (finalPolynomial_uniform S P hn hp) (recoveryPolynomial_envelope S)
 have coeff:=Nat.le_trans (finalSourcePolynomial_legacy S P)
  (Nat.mul_le_mul_left 64 (Nat.add_le_add_right old 32))
 exact Nat.le_trans (final_source_work_bound S P hn hp he) (Nat.mul_le_mul_right _ coeff)

/-- Arbitrary supplied coloring remains explicit at generator level; final
recovery supplies the literal meteredColor implementation above. -/
theorem final_source_absorbed (S : Tree) (P : CommonForest)
 (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true)
 (he : pairwiseEmbeddings S P=true) (q : Nat) (hq : P.length-1≤q)
 (c : Rat) (hc : 2≤c) :
 ((meterRecover S P).work:Rat)≤(recoverySourceEnvelope (leaves S).length:Rat)*c^q := by
 have bound:=Rat.natCast_le_natCast.2 (final_source_uniform S P hn hp he)
 rw [Rat.natCast_mul,Rat.natCast_pow] at bound
 have base:=FinalCutRecovery.qpow_base_mono 2 c (by decide) hc (P.length-1)
 have power:=SourceCoverage.qpow_mono c (by grind) hq
 have coeff :0≤(recoverySourceEnvelope (leaves S).length:Rat):=Rat.natCast_le_natCast.2 (Nat.zero_le _)
 exact Rat.le_trans bound (Rat.mul_le_mul_of_nonneg_left (Rat.le_trans base power) coeff)
end OrdinaryDispatch.RecoveryLocalWork
