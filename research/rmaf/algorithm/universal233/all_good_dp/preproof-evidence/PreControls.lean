import State

namespace AllGoodControls
open RMAF ForestState
def l := Tree.leaf
def n := Tree.node
def quartet := n (n (l 0) (l 1)) (n (l 2) (l 3))
def crossed := [n (l 0) (l 2), n (l 1) (l 3)]
def six := n (l 0) (n (l 1) (n (l 2) (n (l 3) (n (l 4) (l 5)))))
def three := [n (l 0) (l 3), n (l 1) (l 4), n (l 2) (l 5)]
def allGood (T : Option Tree) (ss : List Tree) :=
  proper T ss && ss.all (fun s => targetAgrees T s (leaves s))

theorem empty_input : allGood none [] = true ∧ agrees none [] [] = true ∧
    additionalCost [] [] = 0 := by decide
theorem one_matching : allGood (some (n (l 19) (l 701))) [n (l 19) (l 701)] = true ∧
    agrees (some (n (l 19) (l 701))) [n (l 19) (l 701)] [[19,701]] = true ∧
    additionalCost [n (l 19) (l 701)] [[19,701]] = 0 := by decide
theorem two_clear : allGood (some quartet) [n (l 0) (l 1),n (l 2) (l 3)] = true ∧
    agrees (some quartet) [n (l 0) (l 1),n (l 2) (l 3)] [[0,1],[2,3]] = true ∧
    additionalCost [n (l 0) (l 1),n (l 2) (l 3)] [[0,1],[2,3]] = 0 := by decide
theorem crossed_input : allGood (some quartet) crossed = true ∧
    agrees (some quartet) crossed [[0,2],[1],[3]] = true ∧
    additionalCost crossed [[0,2],[1],[3]] = 1 ∧
    agrees (some quartet) crossed [[0,2],[1,3]] = false := by decide
theorem six_input : allGood (some six) three = true ∧
    agrees (some six) three [[0],[1],[2,5],[3],[4]] = true ∧
    additionalCost three [[0],[1],[2,5],[3],[4]] = 2 := by decide
theorem permuted_input :
    allGood (some (n (n (l 31) (l 7)) (n (l 501) (l 83))))
      [n (l 83) (l 7),n (l 501) (l 31)] = true ∧
    agrees (some (n (n (l 31) (l 7)) (n (l 501) (l 83))))
      [n (l 83) (l 7),n (l 501) (l 31)] [[83,7],[501],[31]] = true := by decide
theorem bad_topology : allGood (some quartet) [n (n (l 0) (l 2)) (n (l 1) (l 3))] = false := by decide
end AllGoodControls
