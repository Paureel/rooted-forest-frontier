import Std
namespace FinalCutClean
structure Certificate where
 vertices : List String
 cuts : List String
 components : List (List Nat)
 deriving DecidableEq, Repr
private def pairCertificate : Certificate := ⟨["","0","1"],["0"],[[1],[0]]⟩
theorem pair_cost : pairCertificate.cuts.length = 1 := by decide
theorem root_retained : pairCertificate.vertices.contains "" = true := by decide
theorem singleton_cost : [([0] : List Nat)].length-1 = 0 := by decide
theorem inner_order_counts : ([0,2] : List Nat).count 0 = ([2,0] : List Nat).count 0 := by decide
theorem repeated_component_visible : ([[0],[1],[1]] : List (List Nat)).length = 3 := by decide
end FinalCutClean
