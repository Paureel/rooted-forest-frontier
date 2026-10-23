import Case322Controls
namespace Universal233.Rule5Case322.Controls
open RMAF Universal233.Rule5Case322 Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
set_option maxRecDepth 20000

theorem i_uniform_F_cover (F : List (List Nat)) (ha : agreement iT iS F = true) :
 ∃ P, P ∈ typeIChildren iT iS 0 1 iqa [true,true,true,false] [true,true,false] ∧ OriginalCover iT iS F P := by
 apply actual_typeI_cover
   (X := .node (.leaf 3) (.node (.leaf 4) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7)))))
   (w := []) (a := 0) (b := 1) (c := 2)
   (U := .leaf 5) (V := .leaf 6)
   (W := .node (.leaf 5) (.node (.leaf 7) (.node (.leaf 3) (.leaf 2))))
   (z := [true,true,true])
 all_goals first | exact ha | exact ⟨[true,false],Or.inl rfl⟩ | rfl | decide |
   (intro x; simp [iT,iS,iqa,leaves]; omega)

theorem ii_bside_geometry : ∀ q, q ∈ iiqs → ∃ U W r,
 q ∈ cuts iiT 1 2 ∧ subtree iiT q = some U ∧ subtree iiT r = some W ∧
 (∀ x, x ∈ leaves U → x ∈ leaves (.node (.leaf 5) (.node (.leaf 8) (.leaf 9)))) ∧
 (∀ x, x ∈ leaves U → x ∈ leaves W) ∧ 1 ∈ leaves W ∧ 2 ∉ leaves W := by
 intro q hq
 have eq : q = [false,false,false,false] ∨ q = [false,false,true] := by simpa [iiqs] using hq
 rcases eq with rfl | rfl
 · refine ⟨.leaf 5,.node (.leaf 5) (.node (.leaf 0) (.leaf 1)),[false,false,false],?_,?_,?_,?_,?_,?_,?_⟩
   all_goals first | rfl | decide | (intro x; simp [leaves]; omega)
 · refine ⟨.leaf 8,.node (.node (.leaf 5) (.node (.leaf 0) (.leaf 1))) (.leaf 8),[false,false],?_,?_,?_,?_,?_,?_,?_⟩
   all_goals first | rfl | decide | (intro x; simp [leaves]; omega)

theorem ii_uniform_F_cover (F : List (List Nat)) (ha : agreement iiT iiS F = true) :
 ∃ P, P ∈ typeIIChildren iiT iiS 0 1 iiqa iiqs ∧ OriginalCover iiT iiS F P := by
 apply actual_typeII_cover (X := .node (.leaf 5) (.node (.leaf 8) (.leaf 9)))
   (w := []) (a := 0) (b := 1) (c := 2)
 all_goals first | exact ha | exact ii_bside_geometry | exact ⟨[false,false,false,true],Or.inl rfl⟩ | rfl | decide |
   (intro x; simp [iiT,iiS,iiqa,leaves]; omega)

theorem iii_uniform_F_cover (F : List (List Nat)) (ha : agreement iiiT iiiS F = true) :
 ∃ P, P ∈ typeIIChildren iiiT iiiS 0 1 iiiqa [[true,true,true]] ∧ OriginalCover iiiT iiiS F P := by
 apply actual_typeIII_cover
   (X := .node (.leaf 3) (.node (.leaf 5) (.node (.leaf 6) (.leaf 7))))
   (w := []) (a := 0) (b := 1) (c := 2)
   (W := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 3) (.leaf 2)))
   (C := .node (.leaf 0) (.leaf 1)) (r := [true,true,true,false])
 all_goals first | exact ha | exact ⟨[true,true,true,false],Or.inl rfl⟩ | rfl | decide |
   (intro x; simp [iiiT,iiiS,iiiqa,leaves]; omega)
end Universal233.Rule5Case322.Controls
