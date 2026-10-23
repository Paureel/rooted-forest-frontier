import RMAF

/- A finite minimum-frontier counterexample in the existing executable model.
The shared model's graph correspondence remains open. No unrestricted
algorithm or improved exponent is asserted. Kernel decide only. -/
namespace PaidCoverFailedFrontier
open RMAF
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def target : Tree := .node
  (.node (.node (.node (.leaf 3) (.leaf 4)) (.leaf 2)) (.leaf 1)) (.leaf 0)
def source : Tree := .node
  (.node (.node (.leaf 1) (.leaf 4)) (.leaf 2)) (.node (.leaf 0) (.leaf 3))

def oneCutParts : List (List (List Nat)) :=
  [[[1,2,4],[0,3]], [[1,4],[0,2,3]], [[1],[0,2,3,4]],
   [[4],[0,1,2,3]], [[2],[0,1,3,4]], [[0,3],[1,2,4]],
   [[0],[1,2,3,4]], [[3],[0,1,2,4]]]

def terminal (bs : List (List Nat)) : Bool :=
  bs.all (fun b => b.length == 3 || restrictionAgrees target source b)

def firstFrontier : List (List (List Nat)) := oneCutParts.filter terminal

def refines (bs coarse : List (List Nat)) : Bool :=
  bs.all (fun b => coarse.any (fun c => b.all (fun x => c.contains x)))

def valid (coarse : Option (List (List Nat))) (a : List Nat) : Bool :=
  agreement target source (blocks a) &&
    match coarse with
    | none => true
    | some c => refines (blocks a) c

def cutCost (a : List Nat) : Nat := (blocks a).length - 1
def solve (coarse : Option (List (List Nat))) : Option (List Nat) :=
  best cutCost (valid coarse) (assignments 5 5)
def optimum (coarse : Option (List (List Nat))) : Option Nat :=
  (solve coarse).map cutCost

theorem proper_labels :
    (leaves target).Perm [0,1,2,3,4] ∧ (leaves source).Perm [0,1,2,3,4] := by decide

theorem initial_outside_terminal : terminal [[0,1,2,3,4]] = false := by decide

theorem exact_one_cut_class_filter :
    firstFrontier = [[[1,2,4],[0,3]], [[1,4],[0,2,3]], [[0,3],[1,2,4]]] := by decide

theorem parent_two_cut_witness :
    valid none [0,0,1,2,0] = true ∧ cutCost [0,0,1,2,0] = 2 := by decide

theorem exact_parent_and_frontier_optima :
    optimum none = some 2 ∧
    optimum (some [[1,2,4],[0,3]]) = some 3 ∧
    optimum (some [[1,4],[0,2,3]]) = some 3 ∧
    optimum (some [[0,3],[1,2,4]]) = some 3 := by decide

theorem every_feasible_at_least (coarse : Option (List (List Nat))) (m : Nat)
    (hopt : optimum coarse = some m) (a : List Nat) (hlen : a.length = 5)
    (hbound : ∀ x ∈ a, x < 5) (hvalid : valid coarse a = true) : m ≤ cutCost a := by
  cases hs : solve coarse with
  | none => simp [optimum, hs] at hopt
  | some winner =>
      have hm : cutCost winner = m := by simpa [optimum, hs] using hopt
      have hbest := best_spec cutCost (valid coarse) (assignments 5 5) winner hs
      have hle := hbest.2.2 a (assignments_complete 5 5 a hlen hbound) hvalid
      omega

theorem first_frontier_loses_every_two_cut_assignment (coarse : List (List Nat))
    (hcoarse : coarse ∈ firstFrontier) (a : List Nat) (hlen : a.length = 5)
    (hbound : ∀ x ∈ a, x < 5) (hvalid : valid (some coarse) a = true) :
    3 ≤ cutCost a := by
  rw [exact_one_cut_class_filter] at hcoarse
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcoarse
  rcases hcoarse with h | h | h
  · subst coarse
    exact every_feasible_at_least _ 3 exact_parent_and_frontier_optima.2.1 a hlen hbound hvalid
  · subst coarse
    exact every_feasible_at_least _ 3 exact_parent_and_frontier_optima.2.2.1 a hlen hbound hvalid
  · subst coarse
    exact every_feasible_at_least _ 3 exact_parent_and_frontier_optima.2.2.2 a hlen hbound hvalid

theorem quartet_five_children_fail_paid_mass : 231 < 5 * 100 := by decide
theorem compatible_two_color_mass_passes : 231*100 + 100^2 < 231^2 := by decide
theorem unpaid_query_has_no_strict_budget_decrease (q : Nat) : ¬ q < q := by omega

#print axioms proper_labels
#print axioms initial_outside_terminal
#print axioms exact_one_cut_class_filter
#print axioms parent_two_cut_witness
#print axioms exact_parent_and_frontier_optima
#print axioms every_feasible_at_least
#print axioms first_frontier_loses_every_two_cut_assignment
#print axioms quartet_five_children_fail_paid_mass
#print axioms compatible_two_color_mass_passes
#print axioms unpaid_query_has_no_strict_budget_decrease
end PaidCoverFailedFrontier
