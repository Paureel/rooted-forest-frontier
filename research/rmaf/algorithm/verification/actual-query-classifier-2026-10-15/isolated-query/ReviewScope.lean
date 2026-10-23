import Work
namespace IndependentQueryScope
open Universal233.PaidQueries
def wrong : Nat → Nat → Option (Nat × Nat) := fun _ _ => some (0,999)
def absent : Nat → Nat → Option (Nat × Nat) := fun _ _ => none
theorem unchecked_solver_result :
 (schedule wrong 4 [.hard 2,.hard 2]).answers = some [(0,999),(0,999)] := by decide
theorem missing_completeness :
 (schedule absent 4 [.hard 2,.hard 2]).answers = none := by decide
def conservativeSource (n : Nat) : Nat :=
 (32*n+32)+32+(24*n+8)+(16*n+24)
theorem conservative_source_envelope (n : Nat) : conservativeSource n ≤ 128*(n+1) := by
 unfold conservativeSource
 omega
end IndependentQueryScope
