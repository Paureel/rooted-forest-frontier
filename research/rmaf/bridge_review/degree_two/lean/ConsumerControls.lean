import PartitionRefinement
namespace DegreeTwo.ConsumerControls
open RMAF

def quartet : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def initial : List (List Nat) := [[0,2],[1],[3]]
def refined : List (List Nat) := [[0],[2],[1],[3]]

theorem initial_agreement : agreement quartet quartet initial = true := by decide
theorem refined_agreement : agreement quartet quartet refined = true := by decide
theorem refined_component_count : refined.length = 4 := by decide
theorem initial_component_count : initial.length = 3 := by decide

theorem singleton_zero_nested : EmbSub quartet [0] [0,2] := by
  simp [EmbSub, quartet, minimalVertices, rootedSpan, prependSide]

theorem singleton_two_nested : EmbSub quartet [2] [0,2] := by
  simp [EmbSub, quartet, minimalVertices, rootedSpan, prependSide]

theorem actual_consumer_application :
    agreement quartet quartet refined = true ∧
    ¬ Occupied quartet refined [] ∧
    AvoidsPartition quartet refined (fun _ => False) ∧
    AvoidsPartition quartet refined (fun _ => False) ∧
    refined.length = initial.length + 1 := by
  exact agreement_replace_and_clear quartet quartet [] [[1],[3]] [0,2] [0] [2] []
    (fun _ => False) (fun _ => False) initial_agreement
    (by intro b hb v h; contradiction) (by intro b hb v h; contradiction)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    singleton_zero_nested singleton_two_nested singleton_zero_nested singleton_two_nested
    (by decide) (by decide) (by decide) (by decide) (by decide)

def siblingsInitial : List (List Nat) := [[0,1],[2],[3]]
def singletons : List (List Nat) := [[0],[1],[2],[3]]
def oldMarks (v : Vertex) : Prop := v = [] ∨ v = [true]

theorem siblings_old_marks : AvoidsPartition quartet siblingsInitial oldMarks := by
  simp [AvoidsPartition, AvoidsBlock, siblingsInitial, oldMarks, quartet,
    minimalVertices, rootedSpan, prependSide]

theorem singleton_zero_siblings_nested : EmbSub quartet [0] [0,1] := by
  simp [EmbSub, quartet, minimalVertices, rootedSpan, prependSide]

theorem singleton_one_siblings_nested : EmbSub quartet [1] [0,1] := by
  simp [EmbSub, quartet, minimalVertices, rootedSpan, prependSide]

theorem prior_marks_preserved : AvoidsPartition quartet singletons oldMarks := by
  exact avoidsPartition_replace quartet [] [[2],[3]] [0,1] [0] [1] oldMarks
    siblings_old_marks singleton_zero_siblings_nested singleton_one_siblings_nested

theorem one_cut_clears_sibling_root_and_keeps_marks :
    agreement quartet quartet singletons = true ∧
    ¬ Occupied quartet singletons [false] ∧
    AvoidsPartition quartet singletons oldMarks ∧
    AvoidsPartition quartet singletons oldMarks ∧
    singletons.length = siblingsInitial.length + 1 := by
  exact agreement_replace_and_clear quartet quartet [] [[2],[3]] [0,1] [0] [1] [false]
    oldMarks oldMarks (by decide) siblings_old_marks siblings_old_marks
    (by decide) (by decide) (by decide) (by decide) (by decide)
    singleton_zero_siblings_nested singleton_one_siblings_nested
    singleton_zero_siblings_nested singleton_one_siblings_nested
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem overlap_mutation_rejected :
    agreement quartet quartet [[0],[0,2],[1],[3]] = false := by decide

theorem false_cost_rejected : refined.length ≠ initial.length := by decide

end DegreeTwo.ConsumerControls
