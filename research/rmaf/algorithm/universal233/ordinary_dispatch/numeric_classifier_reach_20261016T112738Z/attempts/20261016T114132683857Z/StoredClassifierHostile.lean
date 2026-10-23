import StoredClassifierControls
namespace OrdinaryDispatch.StoredNumeric.ClassifierReach.Controls
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open OrdinaryDispatch.StoredNumeric.ProducerBinding
-- Four deliberate bad controls; compilation must reject all four.
theorem hostile_free_classifier : (selectBadBits targetBad sourceBad a b).work=0 := by decide
theorem hostile_c_padding_erased : (selectBadBits targetBad sourceBad a b).value.map (fun d=>d.c)=some [false,true,true] := by decide
theorem hostile_duplicate_removed : (badFor targetBad sourceBad [false,true] duplicateList).value.length=1 := by decide
theorem hostile_unmatched_depth (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest) :
 let p:=(contractPairBits c5 c6 commonT commonS).value
 OrientedPath commonT commonS 2 p.1 p.2 ∧
 OrdinaryDispatch.GlobalNumeric.Reach rec 1 (treeValue commonT) (treeValue commonS) 2 (treeValue p.1) (treeValue p.2) 1 :=
 bound_path_bridge rec paddedBudget commonT commonS (BoundPath.next BoundPath.root (actual_common_event rec))
end OrdinaryDispatch.StoredNumeric.ClassifierReach.Controls
