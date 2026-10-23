import ForestPretestSemantics
namespace ForestPretest01
open RMAF
open Universal233

theorem oneCuts_count (ss : List Tree) :
    (oneCuts ss).length = (ss.map (fun s => (DepthOne.edges s).length)).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [oneCuts,ih]

theorem candidates_count (ss : List Tree) :
    (candidates ss).length = 1 + (ss.map (fun s => (DepthOne.edges s).length)).sum := by
  simp [candidates,oneCuts_count,Nat.add_comm]

theorem vertices_leaves (s : Tree) : (DepthOne.vertices s).length + 1 = 2 * (leaves s).length := by
  induction s with
  | leaf x => simp [DepthOne.vertices,leaves]
  | node l r hl hr =>
    simp only [DepthOne.vertices,leaves,List.length_cons,List.length_append,List.length_map]
    omega

theorem edges_leaves (s : Tree) : (DepthOne.edges s).length + 2 = 2 * (leaves s).length := by
  cases s with
  | leaf x => simp [DepthOne.edges,leaves]
  | node l r =>
    have hl := vertices_leaves l
    have hr := vertices_leaves r
    simp only [DepthOne.edges,leaves,List.length_append,List.length_map]
    omega

theorem candidate_linear_bound (ss : List Tree) :
    (candidates ss).length ≤ 1 + 2 * (ss.flatMap leaves).length := by
  rw [candidates_count]
  suffices (ss.map (fun s => (DepthOne.edges s).length)).sum ≤ 2 * (ss.flatMap leaves).length by omega
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have he := edges_leaves s
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
    omega

end ForestPretest01
