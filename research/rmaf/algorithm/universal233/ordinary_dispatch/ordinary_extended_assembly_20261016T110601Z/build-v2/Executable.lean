import RMAF

/-! One-shot executable original-source controls. The vertices are unsuppressed
addresses; a cut records the child of its ORIGINAL directed edge. -/
namespace Universal233.HardParent
open RMAF

def vertices : Tree → List Vertex
  | .leaf _ => [[]]
  | .node l r => [] :: (prependSide false (vertices l) ++ prependSide true (vertices r))

def pendantOriginal (S : Tree) (a b : Nat) : List Vertex :=
  (vertices S).filter fun v => !v.isEmpty &&
    (minimalVertices [a,b] S).contains v.dropLast &&
    !(minimalVertices [a,b] S).contains v

def subtreeLabels : Tree → Vertex → List Nat
  | S, [] => leaves S
  | .leaf _, _ :: _ => []
  | .node l r, s :: v => subtreeLabels (if s then r else l) v

def literalThree (S : Tree) (p q : Vertex) : List (List Nat) :=
  let A := subtreeLabels S p
  let B := subtreeLabels S q
  [A,B,(leaves S).filter fun x => !A.contains x && !B.contains x]

def target4 : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def source4 : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def target5 : Tree := .node target4 (.leaf 4)
def source5 : Tree := .node source4 (.leaf 4)

-- X0 boundary controls. These precede any universal production theorem.
theorem control_root_lca_cuts : pendantOriginal source4 0 1 = [[false,true],[true,true]] := by decide
theorem control_literal_three : literalThree source4 [false,true] [true,true] = [[2],[3],[0,1]] := by decide
theorem control_clean_agreement : agreement target4 source4 [[0,1],[2],[3]] = true := by decide
theorem control_distinct_nontrivial_overlap : pairwiseEmbeddings target4 [[0,2],[1,3]] = false := by decide
theorem control_same_block_pendant_triple : restrictionAgrees target4 source4 [0,1,2] = false := by decide
theorem control_upward_region_cuts : pendantOriginal source5 0 1 = [[false,false,true],[false,true,true]] := by decide
theorem control_upward_region_allowed : agreement target5 source5 [[0,1,4],[2],[3]] = true := by decide
theorem control_upward_literal_three : literalThree source5 [false,false,true] [false,true,true] = [[2],[3],[0,1,4]] := by decide
theorem control_duplicate_source_rejected :
    agreement target4 (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 2)))
      [[0,1],[2],[3]] = false := by decide
end Universal233.HardParent
