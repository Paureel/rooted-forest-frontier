import RuntimeAssembly
import MassControls
import Primitive
import Payload

namespace Universal233.WholeSourceWork.WorkControls
open RMAF VertexGeometry CoreProgram CoreWork WholeSourceMass WholeSourceMass.MassControls

/-- Plants fixed in WORKFILE before this evaluator existed. The large label
is constructed independently; its exact bit length is 181. -/
def huge : Nat := 2^180+17
def unbalanced : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf huge)
def keepAll : Colors := ⟨.keep,.keep,.keep⟩

theorem actual_large_label_membership :
    (meterContains huge [0,huge+1,huge]).value = true ∧
    (meterContains huge [0,huge+1,huge]).work = 12 := by decide

theorem unbalanced_literal_leafList :
    (meterLeafList [huge] unbalanced).value = [[true]] := by decide

theorem root_two_regions :
    (meterColorLabel chain [] 0).value = 0 ∧
    (meterColorLabel chain [] 3).value = 1 := by decide

theorem joint_count_two :
    (meterJointColors cb chain [false] [true]).value.length = 2 := by decide

theorem joint_count_three :
    (meterJointColors cb3 chain3 [false] [true,false]).value.length = 3 := by decide

theorem exact_n_colors_unbalanced :
    (meterWhole unbalanced unbalanced [0,1] [2] keepAll 0).colorCalls = 4 := by decide

theorem actual_clique_eighteen_colors :
    (meterClique tripod tripod ta tb [true] 0).colorCalls = 18 := by decide

theorem actual_chain_twenty_eight_colors :
    (meterChain chain3 chain3 ca cb3 [false] [true,false] 0).colorCalls = 28 := by decide

theorem actual_diagonal_twelve_colors :
    (meterDiagonal chain chain ca cb [false] [true] 0).colorCalls = 12 := by decide

theorem qzero_actual_pruned :
    (meterClique tripod tripod ta tb [true] 0).outputs = [] ∧
    (meterClique tripod tripod ta tb [true] 0).pruned = 3 := by decide

theorem duplicate_no_colors :
    (meterWhole (.node (.leaf huge) (.leaf huge)) unbalanced [huge] [] keepAll 9).colorCalls = 0 := by decide

/-- Three literal generator output occurrences copied as 1 then 2 cells. -/
theorem actual_outer_append_materialized :
    (meterClique (.leaf huge) (.leaf huge) [huge] [] [] 0).outputs.length = 3 ∧
    (meterClique (.leaf huge) (.leaf huge) [huge] [] [] 0).copied = 3 := by decide

theorem actual_common_vertex :
    (meterCliqueSelection tripod ta tb tc).value = some [true] := by decide

theorem actual_q_cap :
    (meterClique tripod tripod ta tb [true] 1000000).work =
      (meterClique tripod tripod ta tb [true] 5).work := by decide

end Universal233.WholeSourceWork.WorkControls
