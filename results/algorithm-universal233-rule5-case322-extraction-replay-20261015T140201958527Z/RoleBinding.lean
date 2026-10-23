import Case322Caller
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322

def swapRole : Role → Role | .target => .source | .source => .target
def swapBranch (c : Branch) : Branch := { c with role := swapRole c.role }

theorem swapRole_twice (r : Role) : swapRole (swapRole r) = r := by cases r <;> rfl
theorem swapBranch_twice (c : Branch) : swapBranch (swapBranch c) = c := by
 cases c with | mk r qs P => cases r <;> rfl

theorem current_swap (T S : Tree) (c : Branch) : current S T (swapBranch c) = current T S c := by
 cases c with | mk r qs P => cases r <;> rfl

theorem sourceForest_swap (T S : Tree) (c : Branch) : sourceForest S T (swapBranch c) = sourceForest T S c := by
 cases c with | mk r qs P => cases r <;> rfl

theorem guard_swap (T S : Tree) (c : Branch) : currentGuard S T (swapBranch c) = currentGuard T S c := by
 cases c with | mk r qs P => cases r <;> rfl

theorem paid_swap (c : Branch) : paid (swapBranch c) = paid c := rfl

theorem callbacks_swap (q : Nat) (cs : List Branch) :
 callbackRequests q (cs.map swapBranch) = callbackRequests q cs := by
 simp [callbackRequests,swapBranch,paid,List.filterMap_map,Function.comp_def] <;> rfl

theorem exactChild_swap {T S : Tree} {c : Branch} {G : List (List Nat)}
 (h : ExactChild T S c G) : ExactChild S T (swapBranch c) G := by
 refine ⟨agreement_roles_swap h.1,h.2.1,?_⟩
 intro H ha href
 exact h.2.2 H (agreement_roles_swap ha) href

/-- Every original cut, original partition, current tree and paid callback is
transported together. Swapping only the input names is not this operation. -/
theorem operational_role_binding (T S : Tree) (c : Branch) :
 (swapBranch c).originalCuts = c.originalCuts ∧ (swapBranch c).partition = c.partition ∧
 current S T (swapBranch c) = current T S c ∧
 currentGuard S T (swapBranch c) = currentGuard T S c ∧ paid (swapBranch c) = paid c := by
 exact ⟨rfl,rfl,current_swap T S c,guard_swap T S c,rfl⟩
end Universal233.Case322Extraction
