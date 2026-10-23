import ForestDefs
namespace GenericForest.Controls
open RMAF ForestState OutputState VertexGeometry Universal233 CoreProgram PaidQueries
def four (i : Nat) : Tree := .node (.node (.leaf i) (.leaf (i+1))) (.node (.leaf (i+2)) (.leaf (i+3)))
def cross (i : Nat) : Tree := .node (.node (.leaf i) (.leaf (i+2))) (.node (.leaf (i+1)) (.leaf (i+3)))
def a : Tree := .node (.leaf 0) (.leaf 2)
def b : Tree := .node (.leaf 1) (.leaf 3)
def ss : List Tree := [a,b]
def table (t s : Tree) (q : Nat) : Option Forest :=
  let F := [[4],[5],[6,7]]
  if agreement t s F && decide (F.length-1 ≤ q) then some F else none
theorem crossed_state : proper (some (four 0)) ss = true ∧
    DepthOne.pretest01 a a = .found none ∧ DepthOne.pretest01 b b = .found none ∧
    agrees (some (four 0)) ss [[0,2],[1,3]] = false ∧
    agrees (some (four 0)) ss [[0],[2],[1,3]] = true ∧
    additionalCost ss [[0],[2],[1,3]] = 1 ∧ overlap (four 0) ss = some ⟨0,1,[]⟩ := by decide
theorem disjoint_one_hard :
    let t := .node (four 0) (cross 4)
    let src := [four 0,four 4]
    (overlap t src = none) ∧
    ((disjointAttempt t src table 2).map Receipt.calls = some [2]) ∧
    ((componentPair t (four 4)).map (fun p => (leaves p.1).length) = some 4) ∧
    (leaves t).length = 8 := by decide
theorem boundaries : proper none [] = true ∧ agrees none [] [] = true ∧
    proper (some (.leaf 7)) [.leaf 7] = true ∧
    agrees (some (.leaf 7)) [.leaf 7] [[7]] = true ∧
    proper (some (.leaf 7)) [] = false ∧
    proper (some (.node (.leaf 7) (.leaf 7))) [.leaf 7] = false := by decide
def tr : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
theorem three_regions : regions [0,1,2] tr [false] = [0,1,2] := by decide
theorem duplicates :
    let os := raw (four 0) ss 0 [] 1
    os.length = 1 ∧ (os++os).length = 2 ∧
    (os.map (fun o => o.sourceCuts.length)) = [1] := by decide
theorem actual_replacement :
    replace ss 0 [[0],[2]] = [.leaf 0,.leaf 2,b] ∧
    replace ss 1 [[1],[3]] = [a,.leaf 1,.leaf 3] := by decide
end GenericForest.Controls
