import Hard2FrontTreeSource
import CommonBranchWork
import Rule4BoundInterface
namespace OrdinaryDispatch.GlobalSourceAssembly
open RMAF ForestState Universal233 WholeSourceWork
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.Hard2SourceWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.EarlyLocalWork

def commonLocalDebit (T S : Tree) (q : Nat) : Nat :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .rejected=>match early T S with
   | .common reverse c=>(commonBranchMeter FastOrdinary.solve (fun _ _ _=>0) q T S reverse c).work
   | _=>0
  | _=>0
 else 0

def commonCoefficient (N : Nat) : Nat :=256*(2*N+1)^2

theorem commonLocalDebit_bound (N : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) :
 commonLocalDebit T S q≤commonCoefficient N := by
 have scale:=Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left (show 2*(leaves T).length+1≤2*N+1 by omega) 2)
 unfold commonLocalDebit
 simp only [hp,ite_true]
 cases pre:DepthOne.pretest01 T S with
 | refused=>exact Nat.zero_le _
 | found e=>exact Nat.zero_le _
 | rejected=>
  have sound:=early_sound T S
  cases he:early T S with
  | common reverse c=>
   rw [he] at sound
   exact Nat.le_trans (commonBranchMeter_local_bound q T S reverse c hp sound) scale
  | one reverse c=>exact Nat.zero_le _
  | high reverse c=>exact Nat.zero_le _
  | rule4Forward s=>exact Nat.zero_le _
  | rule4Reverse s=>exact Nat.zero_le _
  | hard2 c d=>exact Nat.zero_le _
  | refused=>exact Nat.zero_le _

/-- Original forward/reverse Rule4 source at its selected ordinary invocation.
Its forest work is retained and its ordinary callback fee is zero. -/
def rule4LocalDebit (T S : Tree) (q : Nat) : Nat :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .rejected=>
   let actual:=cutoff FastOrdinary.solve q
   match early T S with
   | .rule4Forward s=>(rule4Source actual (fun _ _ _=>0) s q).work
   | .rule4Reverse s=>(rule4Source actual (fun _ _ _=>0) s q).work
   | _=>0
  | _=>0
 else 0

theorem rule4LocalDebit_bound (N Q : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q) :
 (rule4LocalDebit T S q:Rat)≤(rule4SourcePolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have nonneg:0≤(rule4SourcePolynomial N Q:Rat)*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 unfold rule4LocalDebit
 simp only [hp,ite_true]
 cases pre:DepthOne.pretest01 T S with
 | refused=>simpa only [Rat.natCast_ofNat] using nonneg
 | found e=>simpa only [Rat.natCast_ofNat] using nonneg
 | rejected=>
  cases he:early T S with
  | rule4Forward s=>exact rule4Source_bound (cutoff FastOrdinary.solve q) s q N Q size budget
  | rule4Reverse s=>
   have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
   exact rule4Source_bound (cutoff FastOrdinary.solve q) s q N Q (by omega) budget
  | common reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | one reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | high reverse c=>simpa only [Rat.natCast_ofNat] using nonneg
  | hard2 c d=>simpa only [Rat.natCast_ofNat] using nonneg
  | refused=>simpa only [Rat.natCast_ofNat] using nonneg

/-- Explicit PARTIAL local sheet. All terms below are existing actual source
meters. Remaining hard2/Rule5 execution and output-generation bodies are absent. -/
def closedLocalDebit (T S : Tree) (q : Nat) : Nat :=
 (meterFront q T S).work+commonLocalDebit T S q+simpleLocalDebit T S q+
 rule4LocalDebit T S q+hard2FrontLocalDebit T S q

def simpleNatCoefficient (N Q : Nat) : Nat :=simpleLocalPolynomial N+48*(2^50*(N+Q+2)^8)
def closedLocalPolynomial (N Q : Nat) : Nat :=
 prefixCoefficient N+commonCoefficient N+simpleNatCoefficient N Q+rule4SourcePolynomial N Q+
 hard2FrontCoefficient (2*N+3)

theorem simpleSourceCoefficient_le_nat (N Q : Nat) :
 simpleSourceCoefficient N Q≤(simpleNatCoefficient N Q:Rat) := by
 have geom : (3:Rat)*geometric Rule5ActualTrace.base≤48 := by decide +kernel
 have scaled:=Rat.mul_le_mul_of_nonneg_right geom (Rat.natCast_nonneg (a:=2^50*(N+Q+2)^8))
 have added : (simpleLocalPolynomial N:Rat)+3*geometric Rule5ActualTrace.base*(2^50*(N+Q+2)^8:Nat)≤
  (simpleLocalPolynomial N:Rat)+48*(2^50*(N+Q+2)^8:Nat) := Rat.add_le_add_left.mpr scaled
 simpa only [simpleSourceCoefficient,simpleNatCoefficient,forestCoefficient,Rat.natCast_add,
  Rat.natCast_mul,Rat.natCast_ofNat,Rat.mul_assoc] using added

theorem rat_add_bounds {a b c d : Rat} (ab : a≤b) (cd : c≤d) : a+c≤b+d :=
 Rat.le_trans (Rat.add_le_add_right.mpr ab) (Rat.add_le_add_left.mpr cd)

theorem nat_local_exponential (w C q : Nat) (bound : w≤C) :
 (w:Rat)≤(C:Rat)*Rule5ActualTrace.base^q := by
 have a:=Rat.natCast_le_natCast.2 bound
 have b:=Rat.mul_le_mul_of_nonneg_left (call_base_pow_ge_one q) (Rat.natCast_nonneg (a:=C))
 exact Rat.le_trans a (by simpa only [Rat.mul_one] using b)

theorem closedLocalDebit_bound (N Q : Nat) (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) (budget : q≤Q) :
 (closedLocalDebit T S q:Rat)≤(closedLocalPolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have p:=nat_local_exponential _ _ q (prefix_local_cap q T S N hp size)
 have c:=nat_local_exponential _ _ q (commonLocalDebit_bound N T S q hp size)
 have h:=simpleLocalDebit_bound N Q T S q hp size budget
 have hcap:=Rat.mul_le_mul_of_nonneg_right (simpleSourceCoefficient_le_nat N Q)
  (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q))
 have h':=Rat.le_trans h hcap
 have r:=rule4LocalDebit_bound N Q T S q hp size budget
 have f:=nat_local_exponential _ _ q (hard2FrontLocalDebit_bound N T S q hp size)
 have total:=rat_add_bounds (rat_add_bounds (rat_add_bounds (rat_add_bounds p c) h') r) f
 simpa only [closedLocalDebit,closedLocalPolynomial,Rat.natCast_add,Rat.add_mul] using total
end OrdinaryDispatch.GlobalSourceAssembly
