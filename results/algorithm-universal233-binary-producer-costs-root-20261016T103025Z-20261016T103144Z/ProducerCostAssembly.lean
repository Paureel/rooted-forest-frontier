import ProducerRawBinding
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork Universal233.CoreWork

def parentCallCost (N L Q : Nat):=BinaryCaller.callPolynomial N L Q+32*(N+1)^2+20*(N+1)+8

theorem rawParentProducer_ledger
 (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output))
 (N L I D B M Q : Nat) (ip : 1≤I) (qw : q.length≤B) (sc : SourcesWidth L ss)
 (sn : ∀s∈ss,treeNodes (treeValue s)≤N) (caps : ∀io∈ios,BranchCaps N L I D M io)
 (payload : ∀F∈(rawCandidates solve T ss q ios).value,BinaryCaller.Caps N L Q T ss q F) :
 (rawParentProducer solve T ss q ios).work≤rawCallbackWork solve T ss q ios+
  (rawLocalCost N L I D B ss.length M+parentCallCost N L Q)*(ios.length+1)+4 := by
 have a:=rawCandidates_ledger solve T ss q ios N L I D B M ip qw sc sn caps
 have b:=BinaryCaller.raw_parent_global_work N L Q T ss q (rawCandidates solve T ss q ios).value payload
 have n:=rawCandidates_count solve T ss q ios
 have p:=Nat.mul_le_mul_left (parentCallCost N L Q) (Nat.add_le_add_right n 1)
 simp only [parentCallCost] at p
 simp only [rawParentProducer]
 simp only [parentCallCost]
 simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] at a b p ⊢;omega

/-- The actual generation bill is displayed separately, rather than assumed
polynomial. The remaining nonrecursive bill has the explicit 2^q multiplicity. -/
theorem generatedRawParent_ledger
 (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (h : OverlapBits) (q : Bits)
 (N L I D B M Q : Nat) (ip : 1≤I) (qw : q.length≤B) (sc : SourcesWidth L ss)
 (sn : ∀s∈ss,treeNodes (treeValue s)≤N)
 (caps : ∀io∈(branchesProducer t ss h q).value,BranchCaps N L I D M io)
 (payload : ∀F∈(rawCandidates solve (some t) ss q (branchesProducer t ss h q).value).value,
  BinaryCaller.Caps N L Q (some t) ss q F) :
 (generatedRawParent solve t ss h q).work≤(branchesProducer t ss h q).work+
  rawCallbackWork solve (some t) ss q (branchesProducer t ss h q).value+
  (rawLocalCost N L I D B ss.length M+parentCallCost N L Q)*(12*2^(decode q)+1)+8 := by
 have p:=rawParentProducer_ledger solve (some t) ss q (branchesProducer t ss h q).value N L I D B M Q ip qw sc sn caps payload
 have n:=branchesProducer_exponential_count t ss h q
 have m:=Nat.mul_le_mul_left (rawLocalCost N L I D B ss.length M+parentCallCost N L Q) (Nat.add_le_add_right n 1)
 simp only [generatedRawParent];omega

theorem generatedRawParent_generation_paid
 (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (h : OverlapBits) (q : Bits) :
 (branchesProducer t ss h q).work≤(generatedRawParent solve t ss h q).work := by
 simp only [generatedRawParent];omega
end GenericForest.BinaryProducer
