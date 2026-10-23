import Case322Caller
namespace Universal233.Rule5Case322.Controls
open RMAF Universal233.Rule5Case322 Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
set_option maxRecDepth 20000
def iT : Tree := (.node (.leaf 4) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node (.leaf 3) (.leaf 2))))))))))))
def iS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 4) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))))) (.leaf 2))) (.leaf 1))
theorem i_admitted : admitted iT iS 0 1 = true := by decide
def iqa : RMAF.Vertex := [true,false,false]
def iqs : List RMAF.Vertex := [[true,true,false]]
theorem i_current_guards : (typeIIBranches iT iS 0 1 iqa [true] iqs).all (currentGuard iT iS) = true := by decide
theorem i_raw_costs : (typeIIBranches iT iS 0 1 iqa [true] iqs).map paid = [2,1,2] := by decide
def iiT : Tree := (.node ((.node ((.node ((.node (.leaf 5) ((.node (.leaf 0) (.leaf 1))))) (.leaf 8))) (.leaf 2))) (.leaf 9))
def iiS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 5) ((.node (.leaf 8) (.leaf 9))))))) (.leaf 2))) (.leaf 1))
theorem ii_admitted : admitted iiT iiS 0 1 = true := by decide
def iiqa : RMAF.Vertex := [false,false,false,true,false]
def iiqs : List RMAF.Vertex := [[false,false,false,false],[false,false,true]]
theorem ii_current_guards : (typeIIBranches iiT iiS 0 1 iiqa [true] iiqs).all (currentGuard iiT iiS) = true := by decide
theorem ii_raw_costs : (typeIIBranches iiT iiS 0 1 iiqa [true] iiqs).map paid = [2,1,3] := by decide
def iiiT : Tree := (.node (.leaf 6) ((.node (.leaf 5) ((.node (.leaf 7) ((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 3) (.leaf 2))))))))))
def iiiS : Tree := (.node ((.node ((.node (.leaf 0) ((.node (.leaf 3) ((.node (.leaf 5) ((.node (.leaf 6) (.leaf 7))))))))) (.leaf 2))) (.leaf 1))
theorem iii_admitted : admitted iiiT iiiS 0 1 = true := by decide
def iiiqa : RMAF.Vertex := [true,true,true,false,false]
def iiiqs : List RMAF.Vertex := [[true,true,true]]
theorem iii_current_guards : (typeIIBranches iiiT iiiS 0 1 iiiqa [true] iiiqs).all (currentGuard iiiT iiiS) = true := by decide
theorem iii_raw_costs : (typeIIBranches iiiT iiiS 0 1 iiiqa [true] iiiqs).map paid = [2,1,2] := by decide
theorem i_all_current_guards : (typeIBranches iT iS 0 1 iqa [true] [true,true,false] [true,true,true,false]).all (currentGuard iT iS) = true := by decide
theorem i_all_raw_costs : (typeIBranches iT iS 0 1 iqa [true] [true,true,false] [true,true,true,false]).map paid = [2,1,2,2] := by decide
def wrongSavingF : List (List Nat) := [[0],[1,2,3],[4],[5],[6],[7]]
theorem wrongSaving_valid : agreement iT iS wrongSavingF = true := by decide
theorem wrongSaving_a_single : [0] ∈ wrongSavingF := by decide
theorem wrongSaving_b_nonsingle : [1] ∉ wrongSavingF := by decide
theorem wrongSaving_extra2 : (splitTwo wrongSavingF iS [false,false,true] [false,true]).length = wrongSavingF.length+2 := by decide
end Universal233.Rule5Case322.Controls
