import BindingControls
namespace Universal233.Rule5PaidOrdinary.Controls
open RMAF Rule5Case322 Rule5PaidSelector

def eight : Tree := .node
 (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
 (.node (.node (.leaf 4) (.leaf 5)) (.node (.leaf 6) (.leaf 7)))
def cuts3 : List RMAF.Vertex := [[false,false,false],[false,false,true],[false,true,false]]
def cuts4 : List RMAF.Vertex := cuts3++[[false,true,true]]
def child3 : Branch := targetBranch eight cuts3
def child4 : Branch := targetBranch eight cuts4
example : currentGuard eight eight child3=true ∧ currentGuard eight eight child4=true := by decide
example : (requestFor eight eight 5 child3).map PaidRequest.residual=some 2 := by decide
example : (requestFor eight eight 5 child4).map PaidRequest.residual=some 1 := by decide
example : (requestFor eight eight 5 child3).map (fun Q => Q.sources.length)=some 4 := by decide
example : (requestFor eight eight 5 child4).map (fun Q => Q.sources.length)=some 5 := by decide
end Universal233.Rule5PaidOrdinary.Controls
