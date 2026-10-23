import ForestPretest01
namespace ForestPretest01.Controls
open RMAF ForestState ForestPretest01

def t : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def ss : List Tree := [.node (.leaf 0) (.leaf 2),.node (.leaf 1) (.leaf 3)]
def witness : Forest := [[0],[2],[1,3]]
example : proper (some t) ss = true ∧ agrees (some t) ss (unchanged ss) = false ∧
    agrees (some t) ss witness = true ∧ additionalCost ss witness = 1 := by decide
example : ∃ F ∈ candidates ss, agrees (some t) ss F = true := by decide
example : pretest01 (some t) ss = .found witness := by decide
example : pretest01 none [] = .found [] := by decide
example : pretest01 (some (.leaf 9)) [.leaf 9] = .found [[9]] := by decide
example : pretest01 none [.leaf 9] = .refused := by decide
example : pretest01 (some (.leaf 9)) [] = .refused := by decide
example : pretest01 (some (.leaf 9)) [.leaf 8] = .refused := by decide
example : pretest01 (some (.node (.leaf 9) (.leaf 9))) [.node (.leaf 9) (.leaf 9)] = .refused := by decide
example : pretest01 (some (.node (.leaf 8) (.leaf 9))) [.leaf 8,.leaf 8] = .refused := by decide

def rejectT : Tree := .node (.node (.leaf 0) (.leaf 1))
  (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.leaf 5)))
def rejectSS : List Tree := [.node (.leaf 0) (.leaf 2),.node (.leaf 1) (.leaf 4),.node (.leaf 3) (.leaf 5)]
example : pretest01 (some rejectT) rejectSS = .rejected := by decide
example : agrees (some rejectT) rejectSS [[0],[2],[1],[4],[3,5]] = true ∧
    additionalCost rejectSS [[0],[2],[1],[4],[3,5]] = 2 := by decide

-- The plant deliberately omits every cut from the first actual source.
def omitFirst : List Forest := unchanged ss :: (oneCuts ss.tail).map ([0,2] :: ·)
example : ∃ F ∈ omitFirst, agrees (some t) ss F = true := by decide
example : witness ∉ omitFirst := by decide

-- Mirror the target root, each target cherry, each source cherry and source order.
def mirrors : Tree → List Tree
  | .leaf a => [.leaf a]
  | .node l r => (mirrors l).flatMap fun a => (mirrors r).flatMap fun b => [.node a b,.node b a]
def sourceMirrors : List (List Tree) :=
  (mirrors (.node (.leaf 0) (.leaf 2))).flatMap fun a => (mirrors (.node (.leaf 1) (.leaf 3))).flatMap fun b => [[a,b],[b,a]]
example : ((mirrors t).all fun u => sourceMirrors.all fun sources =>
  match pretest01 (some u) sources with
  | .found F => agrees (some u) sources F && decide (additionalCost sources F = 1)
  | _ => false) = true := by decide
end ForestPretest01.Controls

namespace ForestPretest01.Controls
open RMAF ForestState ForestPretest01
-- A separate exact finite check of inner/outer coverage: it looks for every
-- witness block up to inner Perm, never just for any cheap answer.
def coversWitness (F : Forest) : Bool := witness.all (fun A => F.any (fun B => decide (A.Perm B)))
example : (candidates ss).any coversWitness = true := by decide
example : omitFirst.all (fun F => !coversWitness F) = true := by decide
end ForestPretest01.Controls
