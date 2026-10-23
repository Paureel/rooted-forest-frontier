import UnitCombineSource
namespace OrdinaryDispatch.OuterSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork Universal233.BothBad
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork
open Universal233.CherryBranching

theorem singletonBudget_mono {n N : Nat} (h:n≤N) : singletonChildBudget n≤singletonChildBudget N := by
 unfold singletonChildBudget singletonPartitionBudget
 repeat first | exact h | exact Nat.le_refl _ | apply Nat.add_le_add | apply Nat.mul_le_mul

theorem unitChildrenMeter_bound (S : Tree) (a b N : Nat) (size:(leaves S).length≤N) :
 (unitChildrenMeter S a b).work≤2*singletonChildBudget N+3 := by
 have x:=Nat.le_trans (singleton_child_work S a) (singletonBudget_mono size)
 have y:=Nat.le_trans (singleton_child_work S b) (singletonBudget_mono size)
 simp only [unitChildrenMeter];omega

theorem unitCallsMeter_bound (S T : Tree) (a b q N : Nat) (size:(leaves S).length≤N) :
 (unitCallsMeter S T a b q).work≤2*singletonChildBudget N+21 := by
 have h:=unitChildrenMeter_bound S a b N size
 simp only [unitCallsMeter,unitChildrenMeter_value,List.length_cons,List.length_nil]
 omega

/-- Successful options carry an actual checked budget, rather than a desired
source fee. This pays the literal score lengths, including both sides of ties. -/
theorem chooseMeter_budget_bound (F G : Option (List (List Nat))) (q Q : Nat) (budget:q≤Q)
 (f:∀A,F=some A→A.length-1≤q) (g:∀A,G=some A→A.length-1≤q) :
 (chooseMeter F G).work≤2*Q+6 := by
 cases F with
 | none=>cases G <;> simp only [chooseMeter] <;> omega
 | some A=>cases G with
  | none=>simp only [chooseMeter];omega
  | some B=>have a:=f A rfl;have b:=g B rfl;simp only [chooseMeter];omega

def combinePolynomial (N Q : Nat) :=
 4*singletonChildBudget N+2*(agreementK N+3*N+16)+2*Q+50

theorem combineSource_nat_bound (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (T S : Tree) (a b q N Q : Nat) (paid : Execution) (hp:DepthOne.proper T S=true)
 (size:(leaves T).length≤N) (budget:q≤Q)
 (sound:∀F,paid.answer=some F→F.length-1≤q) :
 (combineSource actual W T S a b q paid).work≤combinePolynomial N Q+
 childForestDebit actual W T q [singletonChild S a,singletonChild S b] := by
 have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have ssize:(leaves S).length≤N:=by omega
 have cs:=unitChildrenMeter_bound S a b N ssize
 have calls:=unitCallsMeter_bound S T a b q N ssize
 have lc:=ordinary_run_children_local actual (fun _=>0) T S q [singletonChild S a,singletonChild S b] hp
 have ak:agreementK (leaves T).length≤agreementK N:=(simpleBudget_mono size).2.2
 have choose:=chooseMeter_budget_bound (runChildren actual T S q [singletonChild S a,singletonChild S b]) paid.answer q Q budget
  (fun F hF=>(runChildren_sound actual T S q _ F hF).2) sound
 have cl:=unitCalls_length S T a b q
 simp only [List.length_cons,List.length_nil] at lc
 simp only [combineSource,unitChildrenMeter_value,unitCallsMeter_value,
  runChildrenSource,ordinary_run_children_value,combinePolynomial]
 omega

def unitForestCoefficient (N Q : Nat) : Rat :=32*forestCoefficient N Q
def combineCoefficient (N Q : Nat) : Rat :=(combinePolynomial N Q:Rat)+unitForestCoefficient N Q

/-- All affordable unit forests, at their exact residuals from
unitForestDebit_exact, are included. Recursive ordinary W-work stays separate. -/
theorem unitForestDebit_bound (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {c : Candidate} {pr : Priority} (q N Q : Nat) (hp:DepthOne.proper T S=true)
 (sel:CherryBranching.select T S=some (pr,c)) (size:(leaves T).length≤N) (budget:q≤Q) :
 (childForestDebit actual (fun _ _ _=>0) T q [singletonChild S c.a,singletonChild S c.b]:Rat)≤
 unitForestCoefficient N Q*Rule5ActualTrace.base^q := by
 have h:=childForestDebit_local_bound actual T q [singletonChild S c.a,singletonChild S c.b] N Q 2 size budget (by simp)
  (fun x hx=>selected_children_proper hp sel x (by simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx;rcases hx with rfl|rfl <;> simp [branches]))
 have geom:geometric Rule5ActualTrace.base≤16:=by decide +kernel
 have fn:0≤forestCoefficient N Q:=Rat.natCast_nonneg
 have m:=Rat.mul_le_mul_of_nonneg_right geom fn
 have p:=Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_left m (by decide +kernel : (0:Rat)≤2))
  (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 have scale:(2:Rat)*(16*forestCoefficient N Q)*Rule5ActualTrace.base^q=
  unitForestCoefficient N Q*Rule5ActualTrace.base^q:=by
  simp only [unitForestCoefficient,←Rat.mul_assoc,show (2:Rat)*16=32 from by decide +kernel]
 exact Rat.le_trans h (by simpa only [Rat.natCast_ofNat,scale] using p)

theorem combineSource_local_bound (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {c : Candidate} {pr : Priority} (q N Q : Nat) (paid : Execution) (hp:DepthOne.proper T S=true)
 (sel:CherryBranching.select T S=some (pr,c)) (size:(leaves T).length≤N) (budget:q≤Q)
 (sound:∀F,paid.answer=some F→F.length-1≤q) :
 ((combineSource actual (fun _ _ _=>0) T S c.a c.b q paid).work:Rat)≤
 combineCoefficient N Q*Rule5ActualTrace.base^q := by
 have h:=Rat.natCast_le_natCast.2 (combineSource_nat_bound actual (fun _ _ _=>0) T S c.a c.b q N Q paid hp size budget sound)
 rw [Rat.natCast_add] at h
 have f:=unitForestDebit_bound actual q N Q hp sel size budget
 have p:=Rat.mul_le_mul_of_nonneg_left (call_base_pow_ge_one q) (Rat.natCast_nonneg (a:=combinePolynomial N Q))
 rw [Rat.mul_one] at p
 exact Rat.le_trans h (by simpa only [combineCoefficient,Rat.add_mul] using Rat.le_trans (Rat.add_le_add_right.mpr p) (Rat.add_le_add_left.mpr f))
end OrdinaryDispatch.OuterSource
