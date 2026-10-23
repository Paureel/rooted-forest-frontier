import ChildrenTraceProjectionV3

namespace SourceRule4ValuesV3
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.EarlyLocalWork
open SourceLocalValuesV3 SourceChildMetadataV3

theorem all_value {α : Type} (f : α→Charged Bool) (xs : List α) :
    (meterAll f xs).value=xs.all (fun x=>(f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [meterAll,List.all_cons,ih]

theorem filter_value {α : Type} (f : α→Charged Bool) (xs : List α) :
    (meterFilter f xs).value=xs.filter (fun x=>(f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [meterFilter,List.filter_cons,ih]

theorem outside_value (T : Tree) (cuts : List Vertex) (x : Nat) :
    (rule4OutsideMeter T cuts x).value=
      cuts.all (fun p=>!(HardParent.subtreeLabels T p).contains x) := by
  simp only [rule4OutsideMeter,all_value,subtreeLabels_value,contains_value]

theorem partition_value (T : Tree) (cuts : List Vertex) :
    (rule4PartitionMeter T cuts).value=Rule4.literalPartition T cuts := by
  simp only [rule4PartitionMeter,Rule4.literalPartition,blocks_value,
    SourceLocalValuesV3.meterLeaves_value,filter_value,outside_value]

theorem state_value (b : Rule4.Branch) : (rule4StateMeter b).value=b.sourceForest := by
  simp only [rule4StateMeter,Rule4.Branch.sourceForest,Rule4.Branch.partition,
    sourceForest_value,partition_value]

theorem leafAddress_value (a : Nat) (T : Tree) :
    (leafAddressMeter a T).value=Rule4.leafAddress a T := by
  induction T with
  | leaf x => rfl
  | node l r il ir =>
    simp only [leafAddressMeter,Rule4.leafAddress,il,ir]
    cases Rule4.leafAddress a l <;> rfl

end SourceRule4ValuesV3
