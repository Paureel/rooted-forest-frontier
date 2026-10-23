/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- Selected-program interface; four prior selector primitives remain reused. -/
import SlimExpansionGeometryV7
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

theorem iso_sym {T U : Tree} (h : RootedIso T U) : RootedIso U T := by
 induction h with
 | leaf x => exact .leaf x
 | straight hl hr il ir => exact .straight il ir
 | swapped hl hr il ir => exact .swapped ir il

theorem agreement_swap {T U : Tree} {G : List (List Nat)} (h : agreement T U G=true) :
 agreement U T G=true := by
 simp only [agreement,Bool.and_eq_true] at h ⊢
 refine ⟨⟨⟨⟨h.1.1.1.2,h.1.1.1.1⟩,?_⟩,h.2⟩,h.1.2⟩
 apply List.all_eq_true.2
 intro B hB
 have agrees := List.all_eq_true.1 h.1.1.2 B hB
 unfold restrictionAgrees at agrees ⊢
 cases l : restrict B T <;> cases r : restrict B U <;> simp [l,r] at agrees ⊢
 exact iso_same (iso_sym (same_iso agrees))

end IndependentGeometry

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @IndependentGeometry.iso_sym
#print axioms IndependentGeometry.iso_sym
#check @IndependentGeometry.agreement_swap
#print axioms IndependentGeometry.agreement_swap
