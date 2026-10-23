import Runtime01
import Controls

namespace Universal233.DepthOne.ConsumerControls
open RMAF CoreGraph CutRealization

theorem zero_actual_original : RealizedOutput RMAF.Controls.leftTree
    ⟨[leaves RMAF.Controls.leftTree],[]⟩ :=
  (found_original_minimum _ _ none Controls.known_zero).2.1

theorem one_actual_original : RealizedOutput RMAF.Controls.rightTree
    ⟨[[2],[0,1,3]],[[false,true,true]]⟩ :=
  (found_original_minimum _ _ (some [false,true,true]) Controls.known_one).2.1

theorem one_globally_minimum : ∀ F, agreement RMAF.Controls.leftTree RMAF.Controls.rightTree F = true →
    1 ≤ F.length - 1 := (found_original_minimum _ _ (some [false,true,true]) Controls.known_one).2.2.2.2

theorem two_universal_lower_bound : ∀ F, agreement RMAF.Controls.leftTree Controls.crossed F = true →
    2 ≤ F.length - 1 := rejected_lower_bound _ _ Controls.known_two_rejects

theorem singleton_actual_original : RealizedOutput (.leaf 71) ⟨[[71]],[]⟩ :=
  (found_original_minimum _ _ none Controls.singleton_zero).2.1

theorem original_parent_still_valid : Valid RMAF.Controls.rightTree [false,true] := by
  exact ⟨.node (.leaf 1) (.leaf 2),by decide⟩

theorem actual_original_edge_removed :
    ¬ ResidualAdj RMAF.Controls.rightTree [[false,true,true]] [false,true] [false,true,true] := by
  intro h
  have hh := h.2 [false,true,true] (by simp)
  exact hh.1 ⟨by decide,rfl⟩

theorem zero_candidate_count : (candidates (.leaf 71)).length = 1 := by decide
theorem quartet_candidate_count : (candidates Controls.crossed).length = 7 := by decide
theorem core_is_proof_only : candidates Controls.crossed =
    [none,some [false],some [false,false],some [false,true],some [true],some [true,false],some [true,true]] := by decide

end Universal233.DepthOne.ConsumerControls
