import ExecutionWork
namespace Universal233.BothBad.ActualConsumers
open RMAF CoreProgram DispatchControls Precontrols

def selectedEdge : RMAF.Vertex × RMAF.Vertex := ([false],[false,false])
def c233 : Rat := mkRat 233 100

theorem same_labels : ∀ x, x∈leaves S ↔ x∈leaves T := by
  intro x
  simp [leaves,S,T,or_comm,or_left_comm]

theorem clear_AC : BinaryExchange.Disj T A C := by
  apply (VertexGeometry.executable_disjointVertices T A C).1
  decide
theorem clear_BC : BinaryExchange.Disj T B C := by
  apply (VertexGeometry.executable_disjointVertices T B C).1
  decide

theorem literal_selected_vertex : PairGeometry.choose T A B=some (.edge selectedEdge) ∧
    PairGeometry.descendants T selectedEdge.2=D := by decide

theorem actual_trace_mass (solve : ForestSolver) :
    traceMass c233 5 (solvePair solve S T A B C selectedEdge 5).calls≤4*c233^(-4 : Int) :=
  solvePair_actual_mass solve S T A B C selectedEdge 5 c233 (by decide) (by decide)
    (by decide) (by decide) same_labels
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) clear_AC clear_BC

theorem actual_child_budget (a : Call)
    (ha : a∈(solvePair planted S T A B C selectedEdge 5).calls) : a.budget+3≤5 :=
  solvePair_calls_drop planted S T A B C selectedEdge 5 a (by decide) (by decide)
    (fun x hx => (same_labels x).1 hx) (by decide) (by decide) ha

theorem actual_prefix_evaluations : (coreRequests S A B D 5).map CoreRequest.budget=[3,3,5] := by decide
theorem actual_recursive_bill : (profilePair planted Call.budget S T A B C selectedEdge 5).recursiveWork=2 := by decide

theorem actual_minimum_choice (solve : ForestSolver) (IH : ExactSolverHyp solve)
    (F : Forest) (ha : agreement T S F=true)
    (href : SourceCoverage.RefinesBlocks F [A,B,C]) (hq : F.length-1≤5) :
    ∃ H, (solvePair solve S T A B C selectedEdge 5).answer=some H ∧
      agreement T S H=true ∧ H.length-1≤5 ∧ H.length≤F.length :=
  solvePair_conditional_cover solve S T A B C selectedEdge 5 F (by decide) (by decide)
    same_labels (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) clear_AC clear_BC ha href hq IH
end Universal233.BothBad.ActualConsumers
