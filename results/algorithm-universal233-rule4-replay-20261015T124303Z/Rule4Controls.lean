import Rule4Solve

namespace Universal233.Rule4.Controls
open RMAF Universal233.Rule4

def T : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.leaf 4)
def S : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) (.leaf 1)
def raw : RawChoice := ⟨0,1,2,[false,false,true],[false,true]⟩
def chosen : Choice T S := ⟨raw,by decide,by decide⟩
def F : Forest := [[0,3],[1],[2],[4]]
def G : Forest := [[0,1],[2],[3],[4]]
def mirror : Tree → Tree
  | .leaf x => .leaf x
  | .node l r => .node (mirror r) (mirror l)
def swap01 : Tree → Tree
  | .leaf x => .leaf (if x = 0 then 1 else if x = 1 then 0 else x)
  | .node l r => .node (swap01 l) (swap01 r)
def mirrored : Choice (mirror T) (mirror S) :=
  ⟨⟨0,1,2,[true,true,false],[true,false]⟩,by decide,by decide⟩
def endpointSwapped : Choice (swap01 T) (swap01 S) :=
  ⟨⟨1,0,2,[false,false,true],[false,true]⟩,by decide,by decide⟩
def refinesCheck (F Q : Forest) : Bool :=
  F.all (fun B => Q.any (fun C => B.all (C.contains ·)))
def badT : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)
def badS : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 3)) (.leaf 1)
def outsideT : Tree := .node (.leaf 5) T
def outsideS : Tree := .node (.leaf 5) S

theorem actual_admitted : Priority T S := by decide
theorem finite_selector_succeeds : (select T S).isSome = true := by decide
theorem mirrored_selector_succeeds : (select (mirror T) (mirror S)).isSome = true := by decide
theorem endpoint_orientation_succeeds : (select (swap01 T) (swap01 S)).isSome = true := by decide
theorem actual_original_F : agreement T S F = true := by decide
theorem actual_exchanged_G : agreement T S G = true := by decide
theorem original_F_refines_no_branch : ((branches chosen).any (fun b => refinesCheck F b.partition)) = false := by decide
theorem exchanged_G_refines_first : refinesCheck G ((branches chosen)[0]'(by decide)).partition = true := by decide
theorem literal_costs : (branches chosen).map Branch.cost = [2,1,2] := by decide
theorem role_swap_source : ((branches chosen)[2]'(by decide)).source = T := by decide
theorem role_swap_target : ((branches chosen)[2]'(by decide)).target = S := by decide
theorem no_t1_exclusion : (select badT badS).isNone = true := by decide
theorem t1_original_ab_two : (HardParent.pendantOriginal badS 0 1).length = 2 := by decide
theorem t1_swapped_ac_one : (HardParent.pendantOriginal badT 0 2).length = 1 := by decide
theorem source_clearance_collision :
    disjointVertices (minimalVertices [0,3] outsideS) (minimalVertices [2,5] outsideS) = false := by decide
theorem outside_original_F : agreement outsideT outsideS [[0,3,5],[1],[2],[4]] = true := by decide
theorem outside_exchanged_G : agreement outsideT outsideS [[0,1,5],[2],[3],[4]] = true := by decide
theorem ordinary_root_boundary : leaves S = [0,2,3,4,1] := by decide
theorem mass_clear_arithmetic : (23300 : Nat)+20000 = 43300 ∧ (233 : Nat)*233 = 54289 := by decide
#eval callbackMass (233/100 : Rat) 10 (costs T S chosen)
end Universal233.Rule4.Controls
