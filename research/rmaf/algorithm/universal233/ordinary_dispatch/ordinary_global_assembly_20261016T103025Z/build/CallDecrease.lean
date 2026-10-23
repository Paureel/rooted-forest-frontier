import PlanActualMass
namespace Universal233.BothBad
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap RankConsumer

theorem cheapPlan_budget (S T : Tree) (A B C D : List Nat) (q : Nat)
    (cheap opposite : List Output) (e : Entry) (he : e∈cheapPlan S T A B C D q cheap opposite) :
    e.budget+e.output.sourceCuts.length+e.mode.extra=q := by
  cases hg : restrictionAgrees S T (ay A D) && restrictionAgrees S T (an A D) with
  | false =>
    simp [cheapPlan,hg] at he
    rcases he with ha | hb
    · obtain ⟨ho,hm,hb,hq⟩ := entries_sound q .ordinary cheap e ha
      rwa [hm]
    · obtain ⟨ho,hm,hb,hq⟩ := entries_sound q .full opposite e hb
      rwa [hm]
  | true =>
    cases hk : knownOne T S A with
    | none => simp [cheapPlan,hg,hk] at he
    | some F =>
      simp [cheapPlan,hg,hk] at he
      rcases he with ha | hb
      · obtain ⟨ho,hm,hb,hq⟩ := entries_sound q .ordinary cheap e ha
        rwa [hm]
      · obtain ⟨ho,hm,hb,hq⟩ := entries_sound q (.retained A B C F) opposite e hb
        rwa [hm]

theorem plan_budget (S T : Tree) (A B C D : List Nat) (q : Nat)
    (e : Entry) (he : e∈plan S T A B C D q) :
    e.budget+e.output.sourceCuts.length+e.mode.extra=q := by
  unfold plan at he
  split at he
  · simp at he
  · dsimp only at he
    split at he
    · split at he
      · obtain ⟨ho,hm,hb,hq⟩ := entries_sound q .full _ e he
        rwa [hm]
      · exact cheapPlan_budget S T B A C D q _ _ e he
    · exact cheapPlan_budget S T A B C D q _ _ e he

theorem dispatch_cap (solve : ForestSolver) (T S : Tree) (e : Entry) (a : Call)
    (ha : a∈(dispatch solve T S e).calls) : a.budget≤e.budget := by
  cases e with
  | mk o mode b =>
    cases mode with
    | ordinary => exact ordinary_budget_cap solve T S o.partition b a ha
    | full =>
      have he : a=⟨some T,OutputState.sourceForest S o.partition,b⟩ := by simpa [dispatch] using ha
      subst a
      exact Nat.le_refl _
    | retained A B C F =>
      have he : a=⟨ForestGroups.localTarget (some T) B,ForestGroups.owned (OutputState.sourceForest S o.partition) B,b⟩ := by
        simpa [dispatch] using ha
      subst a
      exact Nat.le_refl _

/-- The actual binary planner's callbacks all decrease the ordinary cut budget
by at least3. This is derived for literal calls, not a termination field. -/
theorem solvePair_calls_drop (solve : ForestSolver) (S T : Tree) (A B C : List Nat)
    (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (a : Call)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (hl : ∀ x, x∈leaves S → x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge))
    (ha : a∈(solvePair solve S T A B C edge q).calls) : a.budget+3≤q := by
  change a∈(execute solve T S q (plan S T A B C (PairGeometry.descendants T edge.2) q)).calls at ha
  rw [execute_calls] at ha
  obtain ⟨e,he,ha⟩ := List.mem_flatMap.1 ha
  have cap := dispatch_cap solve T S e a ha
  have paid := plan_budget S T A B C (PairGeometry.descendants T edge.2) q e he
  have source := plan_sources S T A B C edge hs ht hl hp hchoose q e he
  have ranks := selected_ranks S T A B C edge ht hl hp hchoose
  have mincost : 3≤e.output.sourceCuts.length := by
    rcases List.mem_append.1 source with hA | hB
    · have h := generate_color_cost S (cheapColor A B (PairGeometry.descendants T edge.2)) q e.output hA
      change RankDichotomy.inputRank S (cheapColor A B (PairGeometry.descendants T edge.2))≤e.output.sourceCuts.length+1 at h
      rw [ranks.1] at h
      omega
    · have h := generate_color_cost S (cheapColor B A (PairGeometry.descendants T edge.2)) q e.output hB
      change RankDichotomy.inputRank S (cheapColor B A (PairGeometry.descendants T edge.2))≤e.output.sourceCuts.length+1 at h
      rw [ranks.2] at h
      omega
  omega
end Universal233.BothBad
