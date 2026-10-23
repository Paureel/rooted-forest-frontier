import RWLocal
namespace OrdinaryDispatch.RecoveryLocalWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.OptimizerLocalWork

/-- A budget-pruned call still constructs its refusal-free receipt and records
pruned=1. Its four fixed control/record slots are charged. -/
def meterRun : Nat→GTree→List Group→List RMAF.Vertex→Charged Receipt
 | 0=>meterStep (fun _ _ _=>⟨⟨[],[],0,0,1⟩,4⟩)
 | q+1=>meterStep (meterRun q)
@[simp] theorem meterRun_value (q : Nat) (t d c) :
 (meterRun q t d c).value=CoreProgram.run q t d c := by
 induction q generalizing t d c with
 | zero=>exact meterStep_value _ t d c
 | succ q ih=>
  simp only [meterRun,meterStep_value,CoreProgram.run]
  congr 1
  funext t d c
  exact ih t d c

theorem meterRun_records (q : Nat) (t d c) :
 records (meterRun q t d c).value≤3*2^(q+1) := by
 rw [meterRun_value]
 exact CoreWork.run_records_bound q t d c

/-- All raw local source helper fees have been derived in RWTree/RWChoose/
RWLocal. This induction uses no localCharge/initialCharge dominance premise. -/
theorem meterRun_bound (q N : Nat) (t : GTree) (d : List Group) (c : List RMAF.Vertex)
 (within : Within N q t d c) : (meterRun q t d c).work≤16*envelope q (localCap N) := by
 induction q generalizing t d c with
 | zero=>
  have tn:footprint t≤N:=by dsimp only [Within] at within;omega
  have dn:d.length≤N:=by dsimp only [Within] at within;omega
  have cn:c.length≤N:=by dsimp only [Within] at within;omega
  have bound:=meterStep_bound (fun _ _ _=>⟨⟨[],[],0,0,1⟩,4⟩) t d c N 4 1 tn dn cn (by decide)
   (by intro _ _ _;exact Nat.le_refl _) (by intro _ _ _;simp [records])
  change (meterStep (fun _ _ _=>⟨⟨[],[],0,0,1⟩,4⟩) t d c).work≤16*(localCap N+3)
  omega
 | succ q ih=>
  have tn:footprint t≤N:=by dsimp only [Within] at within;omega
  have dn:d.length≤N:=by dsimp only [Within] at within;omega
  have cn:c.length≤N:=by dsimp only [Within] at within;omega
  have callback (g : Group) (next : GTree) (he : CoreProgram.erase g.origin (normalize t)=some next) :
   (meterRun q next (g::d) (g.origin::c)).work≤16*envelope q (localCap N):=
   ih next (g::d) (g.origin::c) (continuation_within N q t d c g next within he)
  have pow : 1≤2^(q+1):=Nat.one_le_pow _ _ (by decide)
  have rp : 1≤3*2^(q+1):=by omega
  have bound:=meterStep_bound (meterRun q) t d c N (16*envelope q (localCap N)) (3*2^(q+1))
   tn dn cn rp callback (meterRun_records q)
  change (meterStep (meterRun q) t d c).work≤16*(localCap N+2*envelope q (localCap N)+3*2^(q+1))
  simp only [Nat.mul_add,Nat.mul_assoc] at bound ⊢
  omega

theorem meterRun_closed (q N : Nat) (t : GTree) (d : List Group) (c : List RMAF.Vertex)
 (within : Within N q t d c) :
 (meterRun q t d c).work≤16*((localCap N+6)*(q+1)*2^(q+1)) :=
 Nat.le_trans (meterRun_bound q N t d c within)
  (Nat.mul_le_mul_left 16 (CoreWork.envelope_closed q (localCap N)))

/-- Explicit versioned source cap: four times the frozen declared cap. This
arithmetic comparison follows the primitive proofs and does not replace them. -/
theorem localCap_eq_four_declared (N : Nat) : localCap N=4*CoreWork.cap N := by
 simp only [localCap,CoreWork.cap,←Nat.mul_assoc]
end OrdinaryDispatch.RecoveryLocalWork
