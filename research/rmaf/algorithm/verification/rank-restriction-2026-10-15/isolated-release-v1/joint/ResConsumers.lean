import ResReconstruction
import ResControls

namespace RestrictionBridge.ConsumerControls
open RMAF RestrictionBridge.Controls

theorem consumes_forward :
    (∀ U ∈ Q, ∃ t s, restrict U T = some t ∧ restrict U T = some s ∧
      (leaves t).Perm U ∧ (leaves s).Perm U ∧ agreement t s (family U F) = true) ∧
    (Q.map (fun U => (family U F).length - 1)).sum = F.length - Q.length := by
  apply forward_decomposition T T F Q
  all_goals first | decide | simp [Refines,F,Q,List.subset_def]

def G (U : List Nat) : List (List Nat) := if U == [0,1] then [[0],[1]] else [[2,3]]
def component (U : List Nat) : Tree :=
  if U == [0,1] then .node (.leaf 0) (.leaf 1) else .node (.leaf 2) (.leaf 3)

theorem consumes_reverse :
    agreement T T (Q.flatMap G) = true ∧
    (Q.map (fun U => (G U).length - 1)).sum = (Q.flatMap G).length - Q.length ∧
    (Q.flatMap G).flatten.Perm (leaves T) ∧ (Q.flatMap G).flatten.Perm (leaves T) := by
  apply reverse_reconstruction T T Q G component component
  all_goals first
    | decide
    | intro U hU
      simp only [Q,List.mem_cons,List.mem_singleton] at hU
      rcases hU with rfl | rfl <;> decide

theorem overlap_failure_preserved : agreement T T Qbad = false := by decide
end RestrictionBridge.ConsumerControls
