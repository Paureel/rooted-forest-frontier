import TreeAddresses
open RMAF LeastEmbedding
namespace SemanticControls
theorem singleton_vertices : vertices (.leaf 7) = [[]] := by decide
theorem singleton_terminals : terminals [7] (.leaf 7) = [[]] := by decide
theorem singleton_occurrence_0 : LeafOccurrence (.leaf 7) [] 7 := by
  apply (mem_terminals_iff.mp (show [] ∈ terminals [7] (.leaf 7) by decide)).elim
  intro y hy
  have he : y = 7 := by simpa using hy.2
  subst y
  exact hy.1
theorem empty_vertices : vertices (.node (.leaf 2) (.leaf 3)) = [[], [false], [true]] := by decide
theorem empty_terminals : terminals [] (.node (.leaf 2) (.leaf 3)) = [] := by decide
theorem empty_occurrence_0 : LeafOccurrence (.node (.leaf 2) (.leaf 3)) [false] 2 := by
  apply (mem_terminals_iff.mp (show [false] ∈ terminals [2] (.node (.leaf 2) (.leaf 3)) by decide)).elim
  intro y hy
  have he : y = 2 := by simpa using hy.2
  subst y
  exact hy.1
theorem empty_occurrence_1 : LeafOccurrence (.node (.leaf 2) (.leaf 3)) [true] 3 := by
  apply (mem_terminals_iff.mp (show [true] ∈ terminals [3] (.node (.leaf 2) (.leaf 3)) by decide)).elim
  intro y hy
  have he : y = 3 := by simpa using hy.2
  subst y
  exact hy.1
theorem absent_vertices : vertices (.node (.leaf 2) (.leaf 3)) = [[], [false], [true]] := by decide
theorem absent_terminals : terminals [9] (.node (.leaf 2) (.leaf 3)) = [] := by decide
theorem absent_occurrence_0 : LeafOccurrence (.node (.leaf 2) (.leaf 3)) [false] 2 := by
  apply (mem_terminals_iff.mp (show [false] ∈ terminals [2] (.node (.leaf 2) (.leaf 3)) by decide)).elim
  intro y hy
  have he : y = 2 := by simpa using hy.2
  subst y
  exact hy.1
theorem absent_occurrence_1 : LeafOccurrence (.node (.leaf 2) (.leaf 3)) [true] 3 := by
  apply (mem_terminals_iff.mp (show [true] ∈ terminals [3] (.node (.leaf 2) (.leaf 3)) by decide)).elim
  intro y hy
  have he : y = 3 := by simpa using hy.2
  subst y
  exact hy.1
theorem duplicates_vertices : vertices (.node (.leaf 5) (.node (.leaf 5) (.leaf 8))) = [[], [false], [true], [true, false], [true, true]] := by decide
theorem duplicates_terminals : terminals [5, 5] (.node (.leaf 5) (.node (.leaf 5) (.leaf 8))) = [[false], [true, false]] := by decide
theorem duplicates_occurrence_0 : LeafOccurrence (.node (.leaf 5) (.node (.leaf 5) (.leaf 8))) [false] 5 := by
  apply (mem_terminals_iff.mp (show [false] ∈ terminals [5] (.node (.leaf 5) (.node (.leaf 5) (.leaf 8))) by decide)).elim
  intro y hy
  have he : y = 5 := by simpa using hy.2
  subst y
  exact hy.1
theorem duplicates_occurrence_1 : LeafOccurrence (.node (.leaf 5) (.node (.leaf 5) (.leaf 8))) [true, false] 5 := by
  apply (mem_terminals_iff.mp (show [true, false] ∈ terminals [5] (.node (.leaf 5) (.node (.leaf 5) (.leaf 8))) by decide)).elim
  intro y hy
  have he : y = 5 := by simpa using hy.2
  subst y
  exact hy.1
theorem duplicates_occurrence_2 : LeafOccurrence (.node (.leaf 5) (.node (.leaf 5) (.leaf 8))) [true, true] 8 := by
  apply (mem_terminals_iff.mp (show [true, true] ∈ terminals [8] (.node (.leaf 5) (.node (.leaf 5) (.leaf 8))) by decide)).elim
  intro y hy
  have he : y = 8 := by simpa using hy.2
  subst y
  exact hy.1
theorem deep_vertices : vertices (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
theorem deep_terminals : terminals [1, 2] (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) = [[true, true, false], [true, true, true]] := by decide
theorem deep_occurrence_0 : LeafOccurrence (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) [false] 9 := by
  apply (mem_terminals_iff.mp (show [false] ∈ terminals [9] (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) by decide)).elim
  intro y hy
  have he : y = 9 := by simpa using hy.2
  subst y
  exact hy.1
theorem deep_occurrence_1 : LeafOccurrence (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) [true, false] 8 := by
  apply (mem_terminals_iff.mp (show [true, false] ∈ terminals [8] (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) by decide)).elim
  intro y hy
  have he : y = 8 := by simpa using hy.2
  subst y
  exact hy.1
theorem deep_occurrence_2 : LeafOccurrence (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) [true, true, false] 1 := by
  apply (mem_terminals_iff.mp (show [true, true, false] ∈ terminals [1] (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) by decide)).elim
  intro y hy
  have he : y = 1 := by simpa using hy.2
  subst y
  exact hy.1
theorem deep_occurrence_3 : LeafOccurrence (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) [true, true, true] 2 := by
  apply (mem_terminals_iff.mp (show [true, true, true] ∈ terminals [2] (.node (.leaf 9) (.node (.leaf 8) (.node (.leaf 1) (.leaf 2)))) by decide)).elim
  intro y hy
  have he : y = 2 := by simpa using hy.2
  subst y
  exact hy.1
theorem crossing_vertices : vertices (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
theorem crossing_terminals : terminals [0, 2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) = [[false, false], [true, false]] := by decide
theorem crossing_occurrence_0 : LeafOccurrence (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [false, false] 0 := by
  apply (mem_terminals_iff.mp (show [false, false] ∈ terminals [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) by decide)).elim
  intro y hy
  have he : y = 0 := by simpa using hy.2
  subst y
  exact hy.1
theorem crossing_occurrence_1 : LeafOccurrence (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [false, true] 1 := by
  apply (mem_terminals_iff.mp (show [false, true] ∈ terminals [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) by decide)).elim
  intro y hy
  have he : y = 1 := by simpa using hy.2
  subst y
  exact hy.1
theorem crossing_occurrence_2 : LeafOccurrence (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [true, false] 2 := by
  apply (mem_terminals_iff.mp (show [true, false] ∈ terminals [2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) by decide)).elim
  intro y hy
  have he : y = 2 := by simpa using hy.2
  subst y
  exact hy.1
theorem crossing_occurrence_3 : LeafOccurrence (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [true, true] 3 := by
  apply (mem_terminals_iff.mp (show [true, true] ∈ terminals [3] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) by decide)).elim
  intro y hy
  have he : y = 3 := by simpa using hy.2
  subst y
  exact hy.1
theorem repeated_labels_two_addresses :
    LeafOccurrence (.node (.leaf 5) (.leaf 5)) [false] 5 ∧
    LeafOccurrence (.node (.leaf 5) (.leaf 5)) [true] 5 ∧
    ([false] : Vertex) ≠ [true] :=
  ⟨.left (.leaf 5), .right (.leaf 5), by decide⟩
theorem invalid_address_rejected :
    ¬ ValidVertex (.node (.leaf 5) (.leaf 5)) [false, false] := by
  intro h
  have hm := mem_vertices_iff.mpr h
  have hn : [false, false] ∉ vertices (.node (.leaf 5) (.leaf 5)) := by decide
  exact hn hm
end SemanticControls
