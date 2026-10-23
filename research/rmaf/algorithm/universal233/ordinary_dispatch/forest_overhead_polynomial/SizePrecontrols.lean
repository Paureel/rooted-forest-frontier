import OverheadBound
namespace GenericForest.FrontierSize.Controls
open RMAF ForestState FrontierWork
set_option maxRecDepth 10000
def t : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def s : Tree := .node (.node (.leaf 0) (.leaf 2)) (.leaf 1)
def fail (_ _ : Tree) (_ : Nat) : Option Forest := none

theorem singleton_size_exact : frontier fail (some t) [s] 2=[((t,s),2)] ∧ (leaves t).length=3 := by decide +kernel

theorem solved_empty : frontier fail (some t) [t] 2=[] := by decide +kernel

theorem malformed_empty : frontier fail (some t) [.leaf 0,.leaf 0] 2=[] := by decide +kernel

theorem support_planted : (leaves s).all (leaves t).contains=true := by decide
end GenericForest.FrontierSize.Controls
