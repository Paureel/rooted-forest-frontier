import Rule4OccurrenceV3

namespace SourceLocalValuesV3
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.EarlyLocalWork
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork
open Universal233.Rule5PrefixLocalWork

theorem meterLeaves_value (T : Tree) : (meterLeaves T).value=leaves T := by
  induction T with
  | leaf x => rfl
  | node l r il ir => simp only [meterLeaves,leaves,il,ir]

theorem prefixLeaves_value (T : Tree) : (leavesMeter T).value=leaves T := by
  induction T with
  | leaf x => rfl
  | node l r il ir => simp only [leavesMeter,leaves,il,ir]

theorem meterMap_value {α β : Type} (f : α→Charged β) (xs : List α) :
    (meterMap f xs).value=xs.map (fun x=>(f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [meterMap,List.map_cons,ih]

theorem excludeOne_value (x : Nat) (xs : List Nat) :
    (excludeOneMeter x xs).value=xs.filter (fun z=>z != x) := by
  induction xs with
  | nil => rfl
  | cons z zs ih => simp only [excludeOneMeter,List.filter_cons,ih]

theorem singletonPartition_value (T : Tree) (x : Nat) :
    (singletonPartitionMeter T x).value=CherryBranching.singletonPartition T x := by
  simp only [singletonPartitionMeter,CherryBranching.singletonPartition,prefixLeaves_value,excludeOne_value]

theorem subtreeLabels_value (T : Tree) (p : Vertex) :
    (subtreeLabelsMeter T p).value=HardParent.subtreeLabels T p := by
  induction p generalizing T with
  | nil => simp only [subtreeLabelsMeter,HardParent.subtreeLabels,prefixLeaves_value]
  | cons side p ih =>
    cases T with
    | leaf x => rfl
    | node l r =>
      simpa only [subtreeLabelsMeter,HardParent.subtreeLabels] using ih (if side then r else l)

theorem blocks_value (T : Tree) (ps : List Vertex) :
    (blocksMeter T ps).value=ps.map (HardParent.subtreeLabels T) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [blocksMeter,List.map_cons,subtreeLabels_value,ih]

end SourceLocalValuesV3
