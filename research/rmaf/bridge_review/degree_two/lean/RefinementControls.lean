import ActualRefinement
import ConsumerControls

namespace DegreeTwo.RefinementControls
open RMAF ConsumerControls

theorem original_partition_consumer : ∃ b0 b1 : List Nat,
    agreement quartet quartet [b0,b1,[1],[3]] = true ∧
    ¬ Occupied quartet [b0,b1,[1],[3]] [] ∧
    [b0,b1,[1],[3]].length = initial.length + 1 := by
  obtain ⟨b0,b1,_,_,_,ha,hv,_,_,hc,_⟩ := actual_partition_split
    quartet quartet [] [[1],[3]] [0,2] [] (fun _ => False) (fun _ => False)
    (by decide) initial_agreement
    (by intro b hb v h; contradiction) (by intro b hb v h; contradiction) (by decide)
  exact ⟨b0,b1,ha,hv,hc⟩

theorem original_marks_consumer : ∃ b0 b1 : List Nat,
    agreement quartet quartet [b0,b1,[2],[3]] = true ∧
    ¬ Occupied quartet [b0,b1,[2],[3]] [false] ∧
    AvoidsPartition quartet [b0,b1,[2],[3]] oldMarks ∧
    AvoidsPartition quartet [b0,b1,[2],[3]] oldMarks := by
  obtain ⟨b0,b1,_,_,_,ha,hv,hmt,hmu,_,_⟩ := actual_partition_split
    quartet quartet [] [[2],[3]] [0,1] [false] oldMarks oldMarks
    (by decide) (by decide) siblings_old_marks siblings_old_marks (by decide)
  exact ⟨b0,b1,ha,hv,hmt,hmu⟩

theorem actual_component_consumer : ∃ b0 b1 : List Nat,
    agreement quartet quartet [b0,b1,[1],[3]] = true ∧
    ¬ Occupied quartet [b0,b1,[1],[3]] [] := by
  obtain ⟨b0,b1,_,_,_,ha,hv,_,_,_,_⟩ := actual_component_partition_split
    quartet quartet [] [[1],[3]] [0,2] [0,1,2,3] []
    (fun _ => False) (fun _ => False) (by decide) initial_agreement
    (by intro b hb v h; contradiction) (by intro b hb v h; contradiction)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨b0,b1,ha,hv⟩

def pair : Tree := .node (.leaf 0) (.leaf 1)
def outside : Tree := .node (.leaf 99) (.node (.leaf 1) (.leaf 0))

theorem unequal_full_labels : leaves pair ≠ leaves outside := by decide

theorem unequal_outside_local_consumer : ∃ b0 b1 : List Nat,
    b0 ≠ [] ∧ b1 ≠ [] ∧ (b0 ++ b1).Perm [0,1] ∧
    restrictionAgrees pair outside b0 = true ∧ restrictionAgrees pair outside b1 = true ∧
    disjointVertices (minimalVertices b0 outside) (minimalVertices b1 outside) = true ∧
    [] ∉ minimalVertices b0 pair ∧ [] ∉ minimalVertices b1 pair := by
  obtain ⟨b0,b1,h0,h1,_,_,hp,_,ha0,ha1,_,_,_,_,_,hdu,hv0,hv1⟩ :=
    actual_two_tree_split pair outside [0,1] [] (by decide) (by decide)
      (by decide) (by decide) (by decide)
  exact ⟨b0,b1,h0,h1,hp,ha0,ha1,hdu,hv0,hv1⟩

theorem actual_addresses_differ :
    minimalVertices [0] pair ≠ minimalVertices [0] outside := by decide

end DegreeTwo.RefinementControls
