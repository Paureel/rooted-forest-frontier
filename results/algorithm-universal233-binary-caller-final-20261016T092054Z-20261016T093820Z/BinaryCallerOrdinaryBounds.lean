import BinaryCallerActual
namespace GenericForest.BinaryCaller
open GenericForest.BinaryProvider GenericForest.ScalarBits GenericForest.CheckCorrespondence
open Universal233.WholeSourceWork Universal233.CoreWork

/-- The actual completed fast ordinary callback supplies its candidate size
before the singleton GenericForest.checked call. The budget is unrestricted
relative to the reduced tree size. Stored-word width is a separate invariant. -/
theorem fast_singleton_candidate_sizes (t s : BinaryProvider.Tree) (q : Bits)
 (F : BinaryProvider.Forest) (N : Nat) (tn : treeNodes (treeValue t)≤N)
 (proper : Universal233.DepthOne.proper (treeValue t) (treeValue s)=true)
 (answer : OrdinaryDispatch.FastOrdinary.solve (labelValue q) (treeValue t) (treeValue s)=some (forestValue F)) :
 F.length≤N ∧ F.flatten.length≤N := by
 have p:=fast_returned_payload (treeValue t) (treeValue s) (labelValue q) (forestValue F) proper answer
 have fl:=p.2.1
 have cells:=p.1.length_eq
 have labels:=leaves_nodes (treeValue t)
 simp only [forestValue_length] at fl
 simp only [forestValue_flatten,blockValue_length] at cells
 constructor <;> omega
end GenericForest.BinaryCaller
