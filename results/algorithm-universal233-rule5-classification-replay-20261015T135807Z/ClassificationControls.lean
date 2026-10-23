import LargeAdmitted
namespace Universal233.Rule5Classification.Controls
open RMAF Universal233.CoreGraph Universal233.Rule5Local Universal233.Rule5Local.Pre
open Universal233.CherryBranching
set_option maxRecDepth 8000

theorem large_selected : selectLarge largeT largeS 0 1 = some [false,true] := by decide
theorem two_selected : selectSizeTwo twoT twoS 0 1 = some ⟨[false,true],9,10⟩ := by decide
theorem outside_selected : selectOutside outsideT outsideS 0 1 = some ⟨[true],9,10⟩ := by decide
theorem large_actual_cherry : CherryAt largeT [true,true,true] 0 1 := rfl
theorem two_actual_cherry : CherryAt twoT [true,true] 0 1 := rfl
theorem outside_actual_cherry : CherryAt outsideT [false] 0 1 := rfl
def largeF : List (List Nat) := [[9,0],[11],[10],[1],[3],[6],[7],[8],[5],[4]]
theorem largeF_valid : agreement largeT largeS largeF = true := by decide
theorem largeF_not_refines : refinesCheck largeF (pendantPartition largeS 0 1) = false := by decide
theorem actual_large_replacement : ∃ G, agreement largeT largeS G = true ∧ G.length ≤ largeF.length ∧
 VertexGeometry.Refines G (pendantPartition largeS 0 1) :=
 admitted_large_exchange large_admitted large_actual_cherry (selectLarge_sound large_selected).1
   (selectLarge_sound large_selected).2.1 (selectLarge_sound large_selected).2.2 largeF_valid
theorem actual_two_cover (F : List (List Nat)) (ha : agreement twoT twoS F = true) :
 ∃ d, d ∈ fiveChildren twoS 0 1 9 10 ∧ feasible twoT twoS d F :=
 admitted_sizeTwo_cover two_admitted two_actual_cherry two_selected ha
theorem actual_outside_cover (F : List (List Nat)) (ha : agreement outsideT outsideS F = true) :
 ∃ d, d ∈ fiveChildren outsideS 0 1 9 10 ∧ feasible outsideT outsideS d F :=
 admitted_outside_cover outside_admitted outside_actual_cherry outside_selected ha
theorem all_five_paid : (fiveChildren twoS 0 1 9 10).map Child.paid = [2,2,2,2,2] := by decide
theorem large_paid : (pendantChild largeS 0 1).paid = 2 := by decide

def mirror : Tree → Tree
 | .leaf x => .leaf x
 | .node l r => .node (mirror r) (mirror l)
theorem large_mirror_admitted : admitted (mirror largeT) (mirror largeS) 1 0 = true := by decide
theorem large_mirror_selected : selectLarge (mirror largeT) (mirror largeS) 1 0 = some [true,false] := by decide
theorem large_mirror_actual : CherryAt (mirror largeT) [false,false,false] 1 0 := rfl
theorem actual_mirror_replacement (F : List (List Nat))
 (ha : agreement (mirror largeT) (mirror largeS) F = true) :
 ∃ G, agreement (mirror largeT) (mirror largeS) G = true ∧ G.length ≤ F.length ∧
 VertexGeometry.Refines G (pendantPartition (mirror largeS) 1 0) :=
 admitted_large_exchange large_mirror_admitted large_mirror_actual (selectLarge_sound large_mirror_selected).1
   (selectLarge_sound large_mirror_selected).2.1 (selectLarge_sound large_mirror_selected).2.2 ha
theorem two_mirror_admitted : admitted (mirror twoT) (mirror twoS) 1 0 = true := by decide
theorem two_mirror_selected : selectSizeTwo (mirror twoT) (mirror twoS) 1 0 = some ⟨[true,false],10,9⟩ := by decide
theorem two_mirror_actual : CherryAt (mirror twoT) [false,false] 1 0 := rfl
theorem actual_mirror_two_cover (F : List (List Nat)) (ha : agreement (mirror twoT) (mirror twoS) F = true) :
 ∃ d, d ∈ fiveChildren (mirror twoS) 1 0 10 9 ∧ feasible (mirror twoT) (mirror twoS) d F :=
 admitted_sizeTwo_cover two_mirror_admitted two_mirror_actual two_mirror_selected ha
theorem outside_mirror_admitted : admitted (mirror outsideT) (mirror outsideS) 1 0 = true := by decide
theorem outside_mirror_selected : selectOutside (mirror outsideT) (mirror outsideS) 1 0 = some ⟨[false],10,9⟩ := by decide
theorem outside_mirror_actual : CherryAt (mirror outsideT) [true] 1 0 := rfl
theorem actual_mirror_outside_cover (F : List (List Nat)) (ha : agreement (mirror outsideT) (mirror outsideS) F = true) :
 ∃ d, d ∈ fiveChildren (mirror outsideS) 1 0 10 9 ∧ feasible (mirror outsideT) (mirror outsideS) d F :=
 admitted_outside_cover outside_mirror_admitted outside_mirror_actual outside_mirror_selected ha

end Universal233.Rule5Classification.Controls
