import CheapPlannerCover
namespace Universal233.BothBad
open RMAF CoreProgram ForestState RestrictionBridge ForestGroups PairAssembly BinaryCheap RankConsumer
open VertexGeometry BinaryExchange

/-- Conditional completeness of the SAME executable planner and dispatcher.
Every original agreement refining the source parents is covered; returned
candidates are no larger. Only the future exact recursive solver is an IH. -/
theorem plan_dispatch_cover (solve : ForestSolver) (S T : Tree) (A B C : List Nat)
    (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (F : Forest)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves S ↔ x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hsource : pairwiseEmbeddings S [A,B,C]=true)
    (hbadA : restrictionAgrees S T A=false) (hbadB : restrictionAgrees S T B=false)
    (hgoodC : restrictionAgrees S T C=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge))
    (hac : Disj T A C) (hbc : Disj T B C)
    (hF : agreement T S F=true) (hRef : SourceCoverage.RefinesBlocks F [A,B,C])
    (hcost : F.length-1≤q) (IH : ExactSolverHyp solve) :
    ∃ e H, e∈plan S T A B C (PairGeometry.descendants T edge.2) q ∧
      (dispatch solve T S e).answer=some H ∧ agreement T S H=true ∧ H.length≤F.length := by
  let D := PairGeometry.descendants T edge.2
  have same' : ∀ x, x∈leaves T ↔ x∈leaves S := fun x => (same x).symm
  obtain ⟨o,ho,href,hw⟩ := selected_binary_core_cover S T A B C edge F hs ht hp hchoose hF hRef q hcost
  have refQ : RestrictionBridge.Refines F o.partition := by
    intro K hK
    obtain ⟨U,hU,hKU⟩ := href K hK
    exact ⟨U,hU,fun x hx => hKU x hx⟩
  have ranks := selected_ranks S T A B C edge ht (fun x hx => (same x).1 hx) hp hchoose
  have hq : 3≤q := by
    by_cases hh : 3≤q
    · exact hh
    have aempty := RankDichotomy.below_rank_outputs_empty S (cheapColor A B D) q (by rw [ranks.1];omega)
    have bempty := RankDichotomy.below_rank_outputs_empty S (cheapColor B A D) q (by rw [ranks.2];omega)
    change o∈(generate S (cheapColor A B D) q).outputs ++ (generate S (cheapColor B A D) q).outputs at ho
    simp [aempty,bempty] at ho
  change o∈outputs S A B D q at ho
  by_cases ha : (fourProbe S (cheapColor A B D)).outputs.isEmpty=true
  · by_cases hb : (fourProbe S (cheapColor B A D)).outputs.isEmpty=true
    · have form : plan S T A B C D q=entries q .full (outputs S A B D q) := by
        simp [plan,show ¬q<3 by omega,ha,hb,outputs,sideOutputs,cheapColor,WholeSourceMass.wholeOutputs]
      have gen : ∃ color, o∈(generate S color q).outputs := by
        rcases List.mem_append.1 ho with hA | hB
        · exact ⟨cheapColor A B D,hA⟩
        · exact ⟨cheapColor B A D,hB⟩
      obtain ⟨color,hgen⟩ := gen
      have hQ := (Assembly.generated_source_valid S color q o hgen).1
      have hbgt := generated_residual_budget T S color o q q F hs ht same' hgen hF refQ hcost
      obtain ⟨H,hH,hAF,hRQ,hB,hmin⟩ := full_candidate solve T S color o q
        (q-o.sourceCuts.length) F hs ht same' hgen hF refQ (by omega)
        (IH _ _ _ (OutputState.sourceForest_proper T S o.partition ht hs same' hQ))
      refine ⟨⟨o,.full,q-o.sourceCuts.length⟩,H,?_,hH,hAF,hmin⟩
      change _∈plan S T A B C D q
      rw [form]
      exact entries_complete q .full _ o ho (by simp only [Mode.extra];omega)
    · have acceptB : fourAccepted S (cheapColor B A D)=true := by
        simp only [fourAccepted]
        cases h : (fourProbe S (cheapColor B A D)).outputs.isEmpty <;> simp_all
      obtain ⟨hp',hsource',hchoose'⟩ := selected_symmetry S T A B C edge ht
        (fun x hx => (same x).1 hx) hp hsource hchoose
      have ho' : o∈outputs S B A D q := by
        rcases List.mem_append.1 ho with hA | hB
        · exact List.mem_append.2 (Or.inr hA)
        · exact List.mem_append.2 (Or.inl hB)
      obtain ⟨e,H,he,hH,hAF,hmin⟩ := cheap_plan_dispatch_cover solve S T B A C edge q o F hs ht same
        hp' hsource' hbadB hbadA hgoodC hchoose' hbc hac acceptB hq hF ho' refQ hcost IH
      refine ⟨e,H,?_,hH,hAF,hmin⟩
      change e∈plan S T A B C D q
      simpa [plan,show ¬q<3 by omega,ha,hb] using he
  · have acceptA : fourAccepted S (cheapColor A B D)=true := by
      simp only [fourAccepted]
      cases h : (fourProbe S (cheapColor A B D)).outputs.isEmpty <;> simp_all
    obtain ⟨e,H,he,hH,hAF,hmin⟩ := cheap_plan_dispatch_cover solve S T A B C edge q o F hs ht same
      hp hsource hbadA hbadB hgoodC hchoose hac hbc acceptA hq hF ho refQ hcost IH
    refine ⟨e,H,?_,hH,hAF,hmin⟩
    change e∈plan S T A B C D q
    simpa [plan,show ¬q<3 by omega,ha] using he

theorem solvePair_conditional_cover (solve : ForestSolver) (S T : Tree) (A B C : List Nat)
    (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (F : Forest)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves S ↔ x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hsource : pairwiseEmbeddings S [A,B,C]=true)
    (hbadA : restrictionAgrees S T A=false) (hbadB : restrictionAgrees S T B=false)
    (hgoodC : restrictionAgrees S T C=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge))
    (hac : Disj T A C) (hbc : Disj T B C)
    (hF : agreement T S F=true) (hRef : SourceCoverage.RefinesBlocks F [A,B,C])
    (hcost : F.length-1≤q) (IH : ExactSolverHyp solve) :
    ∃ H, (solvePair solve S T A B C edge q).answer=some H ∧
      agreement T S H=true ∧ H.length-1≤q ∧ H.length≤F.length := by
  obtain ⟨e,H,he,hH,hAF,hmin⟩ := plan_dispatch_cover solve S T A B C edge q F hs ht same hp hsource
    hbadA hbadB hgoodC hchoose hac hbc hF hRef hcost IH
  obtain ⟨G,hG,hGH⟩ := execute_complete solve T S q _ e he H hH hAF (by omega)
  have hsound := execute_sound solve T S q _ G hG
  exact ⟨G,hG,hsound.1,hsound.2,Nat.le_trans hGH hmin⟩
end Universal233.BothBad
