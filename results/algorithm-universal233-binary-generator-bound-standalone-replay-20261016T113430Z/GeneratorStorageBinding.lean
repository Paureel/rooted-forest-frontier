import GeneratorPrefixStorage
namespace GenericForest.BinaryProducer.Generator
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork Universal233.CoreWork

/-- Instrument only: producer work plus its actual guarded prefix retention
ledger. This definition is not used to compute any solver answer. -/
def generateRetention (S : BinaryProvider.Tree) (color : Bits→Charged Color) (q : Bits) :=
 (generateBits S color q).work+
 if (nodupLabels (leavesCopy S).value).value then
  prefixVolume (fuelBits q (leavesCopy S).value.tail).value (fromTreeBits color [] S).value [] []
 else 0

def retentionCost (W N B C : Nat) := generationCost W N B C+2*retentionCoefficient W (inputResource N)*(N+1)

theorem generateRetention_bound (W N B C : Nat) (S : BinaryProvider.Tree) (color : Bits→Charged Color) (q : Bits)
 (sw : TreeWidth W S) (sn : treeNodes (treeValue S)≤N) (bp : 1≤B) (qw : q.length≤B)
 (cc : ∀x,x.length≤W→(color x).work≤C) :
 generateRetention S color q≤retentionCost W N B C*2^(decode q) := by
 have cost:=generateBits_cost W N B C S color q sw sn bp qw cc
 have fn : (fuelBits q (leavesBits S).tail).value.length≤N:=by
  rw [fuelBits_length];have z:=bitsLeaves_count S
  exact Nat.le_trans (Nat.min_le_right _ _) (by simp only [List.length_tail];omega)
 have fq : (fuelBits q (leavesBits S).tail).value.length≤decode q:=by rw [fuelBits_length];exact Nat.min_le_left _ _
 have stored : Stored W (inputResource N) ((fuelBits q (leavesBits S).tail).value.length+1)
  (fromTreeBits color [] S).value [] []:=⟨initial_state W N color S _ sw sn fn,by simp⟩
 have live:=prefixVolume_bound W (inputResource N) _ _ [] [] stored
 have pow:=Nat.pow_le_pow_right (n:=2) (by decide) (Nat.add_le_add_right fq 1)
 have mul:=Nat.mul_le_mul
  (Nat.mul_le_mul_left (retentionCoefficient W (inputResource N)) (Nat.add_le_add_right fn 1)) pow
 have cap : prefixVolume (fuelBits q (leavesBits S).tail).value (fromTreeBits color [] S).value [] []≤
  (2*retentionCoefficient W (inputResource N)*(N+1))*2^(decode q):=by
  have rearrange : retentionCoefficient W (inputResource N)*(N+1)*2^(decode q+1)=
   (2*retentionCoefficient W (inputResource N)*(N+1))*2^(decode q):=by rw [Nat.pow_succ];ac_rfl
  rw [←rearrange];exact Nat.le_trans live mul
 unfold generateRetention;simp only [leavesCopy_value]
 split <;> unfold retentionCost <;> simp only [Nat.add_mul] <;> omega
end GenericForest.BinaryProducer.Generator
