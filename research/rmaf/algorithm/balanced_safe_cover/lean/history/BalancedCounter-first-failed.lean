import RMAF

/-! Finite executable-model replay of X0's equal-halves counterexample.
RMAF graph correspondence remains the same open import as in RMAF.FORMAL.md.
-/
namespace BalancedCounter
open RMAF

def source : Tree := .node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3)))
def target : Tree := .node (.leaf 0) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
def cover : List (List Nat) := [[0, 1], [2, 3]]
def blockInCover (b : List Nat) : Bool :=
  cover.any (fun c => b.all (fun x => c.contains x))
def refinesCover (bs : List (List Nat)) : Bool := bs.all blockInCover

theorem labels_source : leaves source = [0, 1, 2, 3] := by decide
theorem labels_target : leaves target = [0, 1, 2, 3] := by decide
theorem equal_half_partition : partitionCheck [0, 1, 2, 3] cover = true ∧
    cover.all (fun b => b.length = 2) = true := by decide
theorem all_cover_components_compatible :
    cover.all (restrictionAgrees source target) = true := by decide
theorem original_optimum_two_components :
    (solve 4 source target).map (fun a => (blocks a).length) = some 2 := by decide
theorem original_three_displayed_optima :
    agreement source target [[0, 2, 3], [1]] = true ∧
    agreement source target [[0, 1, 3], [2]] = true ∧
    agreement source target [[0, 1, 2], [3]] = true := by decide
theorem covered_completion_three_components :
    (best (fun a => (blocks a).length)
      (fun a => agreement source target (blocks a) && refinesCover (blocks a))
      (assignments 4 4)).map (fun a => (blocks a).length) = some 3 := by decide
theorem no_original_optimum_survives_finite :
    ((assignments 4 4).filter (fun a =>
      agreement source target (blocks a) && refinesCover (blocks a))).all
      (fun a => 3 ≤ (blocks a).length) = true := by decide

theorem every_cover_refining_assignment_costs_three (a : List Nat)
    (hlen : a.length = 4) (hbound : ∀ x ∈ a, x < 4)
    (hagree : agreement source target (blocks a) = true)
    (hcover : refinesCover (blocks a) = true) : 3 ≤ (blocks a).length := by
  have hm : a ∈ (assignments 4 4).filter (fun a =>
      agreement source target (blocks a) && refinesCover (blocks a)) := by
    exact List.mem_filter.mpr ⟨assignments_complete 4 4 a hlen hbound,
      by simp [hagree, hcover]⟩
  exact List.all_eq_true.mp no_original_optimum_survives_finite a hm

theorem clean_singleton_twin :
    agreement source target [[0, 2, 3], [1]] = true ∧
    ([[0, 2, 3], [1]] : List (List Nat)).length = 2 := by decide

theorem actual_target_overlap_vertices :
    (minimalVertices [0, 1] target).filter
      (fun v => (minimalVertices [2, 3] target).contains v) =
      [[true], [true, false]] := by decide

theorem covered_two_blocks_are_not_agreement :
    agreement source target cover = false := by decide

#print axioms labels_source
#print axioms labels_target
#print axioms equal_half_partition
#print axioms all_cover_components_compatible
#print axioms original_optimum_two_components
#print axioms original_three_displayed_optima
#print axioms covered_completion_three_components
#print axioms no_original_optimum_survives_finite
#print axioms every_cover_refining_assignment_costs_three
#print axioms clean_singleton_twin
#print axioms actual_target_overlap_vertices
#print axioms covered_two_blocks_are_not_agreement
end BalancedCounter
