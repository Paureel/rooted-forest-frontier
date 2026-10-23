import StoredSourceSite
namespace OrdinaryDispatch.StoredNumeric.Controls
open RMAF Universal233.WholeSourceWork Universal233.CoreWork
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer

def padded : Bits := [false,false,false,false]
def zeroTree : GenericForest.BinaryProvider.Tree := .leaf padded
def tinyT : GenericForest.BinaryProvider.Tree := .node (.leaf [true]) (.leaf [false,true])
def tinyS : GenericForest.BinaryProvider.Tree := .node (.leaf [false,true]) (.leaf [true])

theorem padded_fresh_values : decode (freshPair zeroTree zeroTree).value.1=1 ∧
 decode (freshPair zeroTree zeroTree).value.2=2 := by
 have v:=freshPair_value zeroTree zeroTree
 have maximum : OrdinaryCommonSplit.Source.labelMax (leaves (treeValue zeroTree)++leaves (treeValue zeroTree))=0 := by decide
 rw [maximum] at v
 exact v

theorem padded_fresh_lengths : (freshPair zeroTree zeroTree).value.1.length=1 ∧
 (freshPair zeroTree zeroTree).value.2.length=2 := by cbv

theorem positive_padding_retained :
 let T : GenericForest.BinaryProvider.Tree:=.leaf [true,false,false,false]
 (freshPair T T).value.1.length=4 ∧ (freshPair T T).value.2.length=4 := by cbv

theorem copied_max_tie : (maximumCopy [] padded).value=padded ∧ (maximumCopy [] padded).work=55 := by cbv

theorem carry_and_swapped_contract :
 (freshOne (.leaf [true,true,true])).value=[false,false,false,true] ∧
 (contractBits [true] [false,true] [true,true] tinyS).value=.leaf [true,true] := by cbv

theorem marked_projection :
 targetValue (markedBits tinyT [[false,true]] [true] [true,true]).value=
 OrdinaryCommonSplit.marked (treeValue tinyT) [2] 1 3 := by
 exact markedBits_value tinyT [[false,true]] [true] [true,true]

theorem payload_storage :
 let out:=(commonPayloadBits zeroTree zeroTree [padded] [padded] padded padded).value
 out.rho.length≤6 ∧ out.gamma.length≤6 ∧ ∀o,o∈payloadTrees out→OptionWidth 6 o := by
 exact commonPayloadBits_width 4 zeroTree zeroTree [padded] [padded] padded padded
  (by
   intro x hx
   have eq:x=padded:=by simpa only [zeroTree,leavesBits,List.mem_singleton] using hx
   rw [eq]
   change padded.length≤4
   decide)
  (by
   intro x hx
   have eq:x=padded:=by simpa only [zeroTree,leavesBits,List.mem_singleton] using hx
   rw [eq]
   change padded.length≤4
   decide)
  (by decide) (by decide)

theorem padded_budget_subtraction : (subtractBits padded []).value.length=4 ∧ (subtractBits padded [true]).value=[] := by cbv

theorem arbitrary_zero_padding (n : Nat) : decode (List.replicate (n+1) false)=0 ∧
 (List.replicate (n+1) false).length>n := ⟨padded_zero _,by simp⟩
end OrdinaryDispatch.StoredNumeric.Controls
