import ActualProgram
import PreControls

namespace AllGoodDPControls
open RMAF ForestState AllGoodDP AllGoodControls
theorem computed_crossed :
    candidate (some quartet) crossed = [[0,2],[1],[3]] ∧
    changes (solve (List.range crossed.length) (owner crossed) quartet) = 2 ∧
    agrees (some quartet) crossed (candidate (some quartet) crossed) = true ∧
    additionalCost crossed (candidate (some quartet) crossed) = 1 := by decide
theorem computed_six :
    agrees (some six) three (candidate (some six) three) = true ∧
    additionalCost three (candidate (some six) three) = 2 ∧
    changes (solve (List.range three.length) (owner three) six) = 4 := by decide
theorem computed_empty : run none [] = some [] := by decide
theorem computed_matching :
    run (some (n (l 19) (l 701))) [n (l 19) (l 701)] = some [[19,701]] := by decide
theorem computed_clear :
    agrees (some quartet) [n (l 0) (l 1),n (l 2) (l 3)]
      (candidate (some quartet) [n (l 0) (l 1),n (l 2) (l 3)]) = true ∧
    additionalCost [n (l 0) (l 1),n (l 2) (l 3)]
      (candidate (some quartet) [n (l 0) (l 1),n (l 2) (l 3)]) = 0 := by decide
theorem computed_permuted :
    agrees (some (n (n (l 31) (l 7)) (n (l 501) (l 83))))
      [n (l 83) (l 7),n (l 501) (l 31)]
      (candidate (some (n (n (l 31) (l 7)) (n (l 501) (l 83))))
        [n (l 83) (l 7),n (l 501) (l 31)]) = true ∧
    additionalCost [n (l 83) (l 7),n (l 501) (l 31)]
      (candidate (some (n (n (l 31) (l 7)) (n (l 501) (l 83))))
        [n (l 83) (l 7),n (l 501) (l 31)]) = 1 := by decide
theorem rejects_bad : run (some quartet) [n (n (l 0) (l 2)) (n (l 1) (l 3))] = none := by decide
end AllGoodDPControls
