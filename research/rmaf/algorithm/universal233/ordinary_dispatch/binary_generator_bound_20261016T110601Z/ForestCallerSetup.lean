import ForestRecursiveProvider
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork

def leafFuel {A : Type} : List A→Charged Capacity
 | []=>⟨[],1⟩
 | _::xs=>let r:=leafFuel xs;⟨()::r.value,r.work+4⟩
@[simp] theorem leafFuel_length {A : Type} (xs : List A) : (leafFuel xs).value.length=xs.length := by
 induction xs <;> simp_all [leafFuel]
@[simp] theorem leafFuel_cost {A : Type} (xs : List A) : (leafFuel xs).work=4*xs.length+1 := by
 induction xs <;> simp_all [leafFuel,Nat.mul_add,Nat.mul_one]

/-- Concrete paid setup from the actual target leaf spine. Original-input
budget lineage must establish the displayed capacity inequality. -/
def forestFromInput
 (ordinary : BinaryProvider.Tree→BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) : Charged (Option BinaryProvider.Forest):=
 let leaves:=targetLabelsCopy T;let cap:=leafFuel leaves.value
 let r:=forestRunBits ordinary cap.value T ss q
 ⟨r.value,leaves.work+cap.work+r.work+8⟩

theorem forestFromInput_value
 (ordinary : BinaryProvider.Tree→BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (nativeOrdinary : RMAF.Tree→RMAF.Tree→Nat→Option GenericForest.Forest)
 (ordinaryIH : ∀t s b,forestOptionValue (ordinary t s b).value=nativeOrdinary (treeValue t) (treeValue s) (decode b))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits)
 (capacity : decode q≤(targetLabelsCopy T).value.length) :
 forestOptionValue (forestFromInput ordinary T ss q).value=GenericForest.solve nativeOrdinary (targetValue T) (sourcesValue ss) (decode q) := by
 exact forestRunBits_value ordinary nativeOrdinary ordinaryIH (leafFuel (targetLabelsCopy T).value).value T ss q
  (by simpa only [leafFuel_length] using capacity)

theorem forestFromInput_setup_paid
 (ordinary : BinaryProvider.Tree→BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) :
 (forestFromInput ordinary T ss q).work=(targetLabelsCopy T).work+4*(targetLabelsCopy T).value.length+1+
 (forestRunBits ordinary (leafFuel (targetLabelsCopy T).value).value T ss q).work+8 := by
 simp only [forestFromInput,leafFuel_cost];omega
end GenericForest.BinaryProducer
