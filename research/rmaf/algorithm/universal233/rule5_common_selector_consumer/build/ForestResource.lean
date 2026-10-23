import ForestTrace
namespace GenericForest
open RMAF RestrictionBridge ForestState
open Universal233.CoreWork

theorem source_nodes_balance (ss : List Tree) :
    sourceNodes ss + ss.length = 2*((ss.map leaves).flatten.length) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have hs := treeNodes_le_twice_leaves s
    simp only [sourceNodes,List.map_cons,List.sum_cons,List.length_cons,
      List.flatten_cons,List.length_append] at *
    omega

theorem proper_source_size (T : Option Tree) (ss : List Tree) (hp : proper T ss = true) :
    sourceNodes ss + ss.length = 2*(labels T).length := by
  have hh := proper_parts T ss hp
  have he := (checked_flatten_perm (labels T) (ss.map leaves) hh.1 hh.2).length_eq
  rw [source_nodes_balance,he]

namespace Controls
def zeroOrdinaryWork (_ _ : Tree) (_ : Nat) : Nat := 0
theorem empty_work_bill : sourceWork table zeroOrdinaryWork none [] 0 = (4096 : Rat) := by cbv
end Controls
end GenericForest
