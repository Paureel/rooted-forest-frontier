import Executable
namespace Universal233.CherryBranching.Pre
open RMAF Universal233.HardParent

def t1 : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def s1 : Tree := .node (.node (.leaf 0) (.leaf 2)) (.leaf 1)
def t3 : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.node (.leaf 3) (.leaf 4)))
def s3 : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 3)) (.node (.leaf 1) (.leaf 4))
def s3up : Tree := .node s3 (.leaf 5)
def t3up : Tree := .node t3 (.leaf 5)
def post (S : Tree) (a b : Nat) : List (List Nat) :=
 let X := (pendantOriginal S a b).map (subtreeLabels S)
 X ++ [(leaves S).filter fun x => !X.flatten.contains x]

theorem t1_cut : pendantOriginal s1 0 1 = [[false,true]] := by decide
theorem t1_part : post s1 0 1 = [[2],[0,1]] := by decide
theorem t2_cut : pendantOriginal source4 0 1 = [[false,true],[true,true]] := by decide
theorem t3_cut : pendantOriginal s3 0 1 = [[false,false,true],[false,true],[true,true]] := by decide
theorem t3_part : post s3 0 1 = [[2],[3],[4],[0,1]] := by decide
theorem upward_cut : pendantOriginal s3up 0 1 = [[false,false,false,true],[false,false,true],[false,true,true]] := by decide
theorem upward_part : post s3up 0 1 = [[2],[3],[4],[0,1,5]] := by decide
theorem sibling_order : pendantOriginal s3 0 1 = pendantOriginal s3 1 0 := by decide
theorem strict_t1_failure_original : agreement t1 s1 [[0,2],[1]] = true := by decide
theorem t1_replacement : agreement t1 s1 [[0,1],[2]] = true := by decide
theorem no_larger : ([[0,1],[2]] : List (List Nat)).length = [[0,2],[1]].length := by decide
theorem source_disjoint_guard : pairwiseEmbeddings source4 [[0,1],[2,3]] = false := by decide
theorem unpaid_guard : (pendantOriginal s3 0 1).length = 3 := by decide
theorem rho_guard : (post s3up 0 1).flatten.Perm [0,1,2,3,4,5] := by decide
private theorem internal_control : agreement t3 s3 (post s3 0 1) = true := by decide
end Universal233.CherryBranching.Pre
