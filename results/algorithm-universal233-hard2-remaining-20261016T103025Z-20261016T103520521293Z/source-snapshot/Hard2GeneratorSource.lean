import Hard2FullOutputSource
import RWInitial
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram
open OrdinaryDispatch.RecoveryLocalWork

/-- Frozen actual CoreProgram source meter, including initialization, refusal,
all output records and every original-leaf color callback. -/
def generatedOutputsMeter (S : Tree) (color : Nat→Charged Nat) (q : Nat) : Charged (List Output) :=
 let r:=RecoveryLocalWork.meterGenerate S color q
 ⟨r.value.outputs,r.work+4⟩
@[simp] theorem generatedOutputsMeter_value (S : Tree) (color : Nat→Charged Nat) (q : Nat) :
 (generatedOutputsMeter S color q).value=(generate S (fun x=>(color x).value) q).outputs := by
 simp [generatedOutputsMeter]

def generationEnvelope (S : Tree) (q : Nat) : Nat :=
 initialCharge S+16*((RecoveryLocalWork.localCap (inputResource S)+6)*
   (min q ((leaves S).length-1)+1)*2^(min q ((leaves S).length-1)+1))+12

theorem generatedOutputsMeter_bound (S : Tree) (color : Nat→Charged Nat) (q : Nat) :
 (generatedOutputsMeter S color q).work≤generationEnvelope S q+
 ((leaves S).map (fun x=>(color x).work)).sum := by
 have h:=RecoveryLocalWork.meterGenerate_bound S color q
 simp only [generatedOutputsMeter,generationEnvelope]
 omega

theorem generate_output_count (S : Tree) (color : Nat→Nat) (q : Nat) :
 (generate S color q).outputs.length≤3*2^(min q ((leaves S).length-1)+1) := by
 have h:=CoreWork.run_records_bound (min q ((leaves S).length-1)) (fromTree color [] S) [] []
 simp only [records] at h
 by_cases proper:(leaves S).Nodup
 · simp only [generate,proper,ite_true];omega
 · simp only [generate,proper,ite_false,List.length_nil];omega

/-- Append copies each left output occurrence. Duplicate outputs are retained. -/
def appendOutputsMeter (a b : Charged (List Output)) : Charged (List Output) :=
 ⟨a.value++b.value,a.work+b.work+2*a.value.length+4⟩
@[simp] theorem appendOutputsMeter_value (a b : Charged (List Output)) :
 (appendOutputsMeter a b).value=a.value++b.value:=rfl

def wholeOutputsMeter (S T : Tree) (A B : List Nat) (c : Colors) (q : Nat) : Charged (List Output) :=
 generatedOutputsMeter S (meterTagged T A B c) q
@[simp] theorem wholeOutputsMeter_value (S T : Tree) (A B : List Nat) (c : Colors) (q : Nat) :
 (wholeOutputsMeter S T A B c q).value=
 WholeSourceMass.wholeOutputs S A B (localColor T c.a) (localColor T c.b) (localColor T c.c) q := by
 simp [wholeOutputsMeter,WholeSourceMass.wholeOutputs,colors]

theorem charged_color_sum (xs : List Nat) (f : Nat→Charged Nat) (K : Nat)
 (cap : ∀x,x∈xs→(f x).work≤K) : (xs.map (fun x=>(f x).work)).sum≤xs.length*K := by
 induction xs with
 | nil=>simp
 | cons x xs ih=>
  have a:=cap x (by simp)
  have b:=ih (by intro y h;exact cap y (by simp [h]))
  simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
  omega

theorem wholeOutputsMeter_bound (S T : Tree) (A B : List Nat) (c : Colors) (q : Nat) :
 (wholeOutputsMeter S T A B c q).work≤generationEnvelope S q+(leaves S).length*taggedCap T A B c := by
 exact Nat.le_trans (generatedOutputsMeter_bound S (meterTagged T A B c) q)
  (Nat.add_le_add_left (charged_color_sum (leaves S) (meterTagged T A B c) _
    (by intro x _;exact meterTagged_bound T A B c x)) _)
end OrdinaryDispatch.Hard2SourceWork
