import SlimBoundaryHullV3R2
open RMAF
namespace IndependentPaid
theorem blocks_nodup (Q : List (List Nat)) (hn : Q.flatten.Nodup)
 (nonempty : ∀B∈Q,B≠[]) : Q.Nodup := by
 induction Q with
 | nil => simp
 | cons B rest ih =>
  have parts := List.nodup_append.1 (show (B++rest.flatten).Nodup from hn)
  apply List.nodup_cons.2
  constructor
  · intro hB
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B (nonempty B (by simp))
    exact parts.2.2 x hx x (List.mem_flatten.2 ⟨B,hB,hx⟩) rfl
  · exact ih parts.2.1 (fun C hC=>nonempty C (by simp [hC]))

end IndependentPaid

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @IndependentPaid.blocks_nodup
#print axioms IndependentPaid.blocks_nodup
