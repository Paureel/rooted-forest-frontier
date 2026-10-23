import GroupPriority
import GroupControls
namespace ForestGroups.ConsumerControls
open RMAF RestrictionBridge ForestState ForestGroups.Controls

theorem actual_bad_A_one : agrees (localTarget (some target) [0,1,2]) [aS] aF = true ∧
    additionalCost [aS] aF = 1 := by decide

/-- Concrete retained source A with a paid one-cut checker witness, ANY residual
Bforest agreement, and completed singleton C. B's actual pieces overlap. -/
theorem actual_A_any_residual (FB : List (List Nat))
    (hB : agrees (localTarget (some target) [3,4,5,6]) [b1,b2] FB = true) :
    agrees (some target) sources (aF ++ FB ++ cF) = true ∧
    additionalCost sources (aF ++ FB ++ cF) = 1 + additionalCost [b1,b2] FB := by
  exact retained_A_one_plus_Bforest (some target) aS [b1,b2] [.leaf 7]
    [0,1,2] [3,4,5,6] [7] aF FB cF (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      intro t ht
      have eq : target = t := Option.some.inj ht
      subst t
      simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
      repeat' constructor
      all_goals apply (clear_iff _ _).1
      all_goals decide)
    actual_bad_A_one.1 actual_bad_A_one.2 hB (by decide) (by decide)

theorem literal_overlap_and_paid_cost :
    disjointVertices (minimalVertices (leaves b1) target) (minimalVertices (leaves b2) target) = false ∧
    agrees (some target) sources (aF ++ bF ++ cF) = true ∧
    additionalCost sources (aF ++ bF ++ cF) = 3 := by
  have h := actual_A_any_residual bF (by decide)
  exact ⟨by decide,h.1,by simpa [additionalCost,bF] using h.2⟩

example : agrees none [] (([] : List (List Nat)).flatMap (fun _ => [])) = true := by
  apply reverse_reconstruction none [] [] (fun _ => []) (by decide) (by decide)
  · intro s hs; simp at hs
  · intro t ht; simp at ht
  · intro U hU; simp at hU

example : agrees (localTarget (some (.leaf 9)) [9])
    (owned [.leaf 9] [9]) (family [9] [[9]]) = true := by
  exact local_forward (some (.leaf 9)) [.leaf 9] [[9]] [[9]]
    (by decide) (by decide) (by
      intro s hs
      have eq : s = .leaf 9 := by simpa using hs
      subst s
      exact ⟨[9],by simp,by decide⟩)
    [9] (by simp)
end ForestGroups.ConsumerControls

namespace ForestGroups.ConsumerControls
open RMAF RestrictionBridge ForestState ForestGroups.Controls

theorem ordinary_local_checks : ∀ U ∈ ordinaryGroups,
    agrees (localTarget (some ordinary) U) (owned ordinarySources U)
      (family U ordinaryGroups) = true := by
  apply forward_decomposition (some ordinary) ordinarySources ordinaryGroups ordinaryGroups
    (by decide) (by decide)
  intro s hs
  simp only [ordinarySources,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨[0,1],by decide,by decide⟩
  · exact ⟨[2,3],by decide,by decide⟩

example : (ordinaryGroups.map (fun U => additionalCost (owned ordinarySources U)
    (family U ordinaryGroups))).sum = additionalCost ordinarySources ordinaryGroups := by
  apply forward_exact_cost (some ordinary) ordinarySources ordinaryGroups ordinaryGroups
    (by decide) (by decide)
  intro s hs
  simp only [ordinarySources,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨[0,1],by decide,by decide⟩
  · exact ⟨[2,3],by decide,by decide⟩

example : ((List.reverse groups).map (fun U =>
    additionalCost (owned (List.reverse sources) U)
      (family U (List.reverse (aF ++ bF ++ cF))))).sum = 3 := by decide
end ForestGroups.ConsumerControls
