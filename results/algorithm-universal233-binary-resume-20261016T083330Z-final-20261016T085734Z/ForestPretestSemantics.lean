import ForestCoverage
namespace ForestPretest01
open RMAF ForestState

/-- A returned forest is globally minimum among every actual full-state AF. -/
theorem found_globally_minimum (T : Option Tree) (ss : List Tree) (F : Forest)
    (h : pretest01 T ss = .found F) :
    agrees T ss F = true ∧ additionalCost ss F ≤ 1 ∧
      ∀ G, agrees T ss G = true → additionalCost ss F ≤ additionalCost ss G := by
  obtain ⟨hp,hF,ha,hsmall,hmin⟩ := found_spec T ss F h
  refine ⟨ha,hsmall,?_⟩
  intro G hG
  by_cases hc : additionalCost ss G ≤ 1
  · obtain ⟨H,hH,_,hHa,hcost⟩ := universal_coverage T ss G hG hc
    rw [←hcost]
    exact hmin H hH hHa
  · omega

/-- Rejection excludes every actual AF of additional cost zero or one. -/
theorem rejected_lower_bound (T : Option Tree) (ss : List Tree)
    (h : pretest01 T ss = .rejected) :
    proper T ss = true ∧ ∀ F, agrees T ss F = true → 2 ≤ additionalCost ss F := by
  obtain ⟨hp,hnone⟩ := rejected_spec T ss h
  refine ⟨hp,?_⟩
  intro F hF
  by_cases hc : additionalCost ss F ≤ 1
  · obtain ⟨G,hG,_,hGa,_⟩ := universal_coverage T ss F hF hc
    simp [hnone G hG] at hGa
  · omega

/-- Every actual cost≤1 witness forces a found globally minimum forest. -/
theorem pretest_complete (T : Option Tree) (ss : List Tree) (F : Forest)
    (ha : agrees T ss F = true) (hc : additionalCost ss F ≤ 1) :
    ∃ G, pretest01 T ss = .found G ∧ agrees T ss G = true ∧
      additionalCost ss G ≤ additionalCost ss F ∧
      ∀ H, agrees T ss H = true → additionalCost ss G ≤ additionalCost ss H := by
  obtain ⟨H,hH,_,hHa,hcost⟩ := universal_coverage T ss F ha hc
  obtain ⟨G,hbest⟩ := best_exists (additionalCost ss) (agrees T ss) (candidates ss) H hH hHa
  have hp := (agrees_parts T ss F ha).1
  have hfound : pretest01 T ss = .found G := by simp [pretest01,hp,hbest]
  obtain ⟨hGa,hsmall,hmin⟩ := found_globally_minimum T ss G hfound
  exact ⟨G,hfound,hGa,hmin F ha,hmin⟩

end ForestPretest01
