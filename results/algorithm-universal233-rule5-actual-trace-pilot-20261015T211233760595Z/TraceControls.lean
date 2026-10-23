import QuerySizes
import Rule5PreControls
namespace Universal233.Rule5ActualTrace.Controls
open RMAF ForestState Rule5Local.Pre Rule5FinalClassification Rule5OrdinaryDispatch
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
def fail : Ordinary := fun _ _ _ => none
def fourT : Tree := .node (.node (.node (.node (.node (.leaf 14) (.node (.leaf 0) (.leaf 1))) (.leaf 17)) (.leaf 15)) (.leaf 2)) (.leaf 16)
def fourS : Tree := .node (.node (.node (.leaf 0) (.node (.leaf 14) (.node (.leaf 17) (.node (.leaf 15) (.leaf 16))))) (.leaf 2)) (.leaf 1)
def typeIT : Tree := .node (.node (.leaf 14) (.node (.leaf 0) (.leaf 1))) (.node (.leaf 17) (.node (.leaf 18) (.leaf 2)))
def typeIS : Tree := .node (.node (.node (.leaf 0) (.node (.node (.leaf 14) (.leaf 17)) (.leaf 18))) (.leaf 2)) (.leaf 1)
def fixtures : List (Tree×Tree×Nat) :=
 [(largeT,largeS,1),(twoT,twoS,1),(outsideT,outsideS,1),
  (firstT,firstS,1),(thirdT,thirdS,1),(commonT,commonS,2),(sixT,sixS,3),
  (fourT,fourS,3),(typeIT,typeIS,3)]
def kind : Calls→Nat
 | .forestJobs _ => 1 | .direct _ => 2 | .paidRequests _ => 3
 | .selectorRefused => 4 | .paidBuilderRefused => 5
def outerPayments : Calls→List Nat
 | .forestJobs js => js.map (fun j => j.child.paid)
 | .direct _ => []
 | .paidRequests js => js.map (fun j => j.branch.originalCuts.length)
 | _ => []
def paidCheck (q : Nat) : Calls→Bool
 | .forestJobs js => js.all fun j => decide (j.residual+j.child.paid=q) && decide (j.residual<q)
 | .direct js => js.all fun j => decide (q-j.budget=1) && decide (j.budget<q)
 | .paidRequests js => js.all fun j => decide (j.residual+j.branch.originalCuts.length=q) && decide (j.residual<q)
 | _ => false
def runtimeChecks : List (String×Bool) :=
 [("literal_kind",fixtures.all fun f => kind (dispatchTrace fail f.1 f.2.1 0 1 4).calls==f.2.2),
  ("actual_value",fixtures.all fun f => (dispatchTrace fail f.1 f.2.1 0 1 4).value==dispatch fail f.1 f.2.1 0 1 4),
  ("zero_budget",fixtures.all fun f => (dispatchTrace fail f.1 f.2.1 0 1 0).value==.answered none),
  ("full_original_debits",fixtures.all fun f => paidCheck 4 (dispatchTrace fail f.1 f.2.1 0 1 4).calls),
  ("actual_mass",fixtures.all fun f => decide (mass base 4 (queries fail (dispatchTrace fail f.1 f.2.1 0 1 4).calls)≤gamma base)),
  ("actual_sizes",fixtures.all fun f =>
    (queries fail (dispatchTrace fail f.1 f.2.1 0 1 4).calls).all fun j =>
      decide (j.2<4) && decide ((leaves j.1.1).length≤(leaves f.1).length) &&
      decide ((leaves j.1.2).length≤(leaves f.1).length)),
  ("direct_failures_retained",(queries fail (dispatchTrace fail commonT commonS 0 1 4).calls).length==2),
  ("direct_budget_three",(queries fail (dispatchTrace fail commonT commonS 0 1 4).calls).map Prod.snd==[3,3]),
  ("second_actual_cut_costs",outerPayments (dispatchTrace fail sixT sixS 0 1 4).calls==[2,1,3]),
  ("second_four_cut_state",outerPayments (dispatchTrace fail fourT fourS 0 1 4).calls==[2,1,4]),
  ("second_typeI_four_requests",outerPayments (dispatchTrace fail typeIT typeIS 0 1 4).calls==[2,1,2,2]),
  ("new_source_guards",Rule5Local.admitted fourT fourS 0 1 && Rule5Local.admitted typeIT typeIS 0 1),
  ("duplicates_retained",match (dispatchTrace fail commonT commonS 0 1 4).calls with
    | .direct js => (queries fail (.direct (js++js))).length==2*(queries fail (.direct js)).length
    | _ => false)]
#eval runtimeChecks
#eval ("PASS_LITERAL_RULE5_TRACE_CONTROLS",runtimeChecks.all Prod.snd)
#eval fixtures.map fun f => (kind (dispatchTrace fail f.1 f.2.1 0 1 4).calls,
 outerPayments (dispatchTrace fail f.1 f.2.1 0 1 4).calls,
 (queries fail (dispatchTrace fail f.1 f.2.1 0 1 4).calls).map Prod.snd)
end Universal233.Rule5ActualTrace.Controls
