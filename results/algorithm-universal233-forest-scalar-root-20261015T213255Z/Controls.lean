import Optimality01
namespace OrdinaryCommonSplit.Controls
open RMAF Universal233

def tX : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def sX : Tree := .node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def tY : Tree := .node (.node (.leaf 3) (.leaf 4)) (.leaf 5)
def sY : Tree := .node (.leaf 3) (.node (.leaf 4) (.leaf 5))
def T : Tree := .node tX tY
def S : Tree := .node sX sY
def X : List Nat := [0,1,2]
def Y : List Nat := [3,4,5]
def markedXT : Tree := .node tX (.leaf 6)
def markedXS : Tree := .node sX (.leaf 6)
def markedYT : Tree := .node tY (.leaf 7)
def markedYS : Tree := .node sY (.leaf 7)
def wrongMarkedXT : Tree := .node (.node (.node (.leaf 0) (.leaf 6)) (.leaf 1)) (.leaf 2)
def highMarkedT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 6))
def highMarkedS : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 6))
def interleaved : Tree := .node (.node (.leaf 0) (.leaf 3))
  (.node (.node (.leaf 1) (.leaf 4)) (.node (.leaf 2) (.leaf 5)))

def foundOne (t s : Tree) : Bool := match DepthOne.pretest01 t s with
  | .found (some _) => true
  | _ => false

theorem proper_split : partitionCheck (leaves T) [X,Y]=true ∧
    partitionCheck (leaves S) [X,Y]=true ∧ pairwiseEmbeddings T [X,Y]=true ∧
    pairwiseEmbeddings S [X,Y]=true := by decide
theorem local_cut_units : foundOne tX sX=true ∧ foundOne tY sY=true := by decide
theorem marked_stable_units : foundOne markedXT markedXS=true ∧ foundOne markedYT markedYS=true := by decide
theorem global_two_cut_witness : agreement T S [[0,1,3,4],[2],[5]]=true ∧
    ([[0,1,3,4],[2],[5]] : List (List Nat)).length-1=2 := by decide
theorem global_at_least_two : DepthOne.pretest01 T S=.rejected := by decide
theorem wrong_marker_preserves_local_but_moves_attachment :
    (restrict X wrongMarkedXT).any (sameShape tX)=true ∧
    sameShape wrongMarkedXT markedXT=false := by decide
theorem root_child_orientation :
    sameShape (.node (.leaf 6) tX) markedXT=true ∧
    agreement (.node tX tY) (.node sY sX) [[0,1,3,4],[2],[5]]=true := by decide
theorem marked_increase_really_occurs : DepthOne.pretest01 highMarkedT highMarkedS=.rejected ∧
    agreement highMarkedT highMarkedS [[0,1],[2],[6]]=true ∧
    foundOne (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)) tX=true := by decide
theorem missing_target_guard : partitionCheck (leaves interleaved) [X,Y]=true ∧
    pairwiseEmbeddings interleaved [X,Y]=false := by decide
end OrdinaryCommonSplit.Controls
