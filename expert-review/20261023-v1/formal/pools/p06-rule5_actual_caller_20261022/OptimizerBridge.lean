import CallbackBridge
import BOOptimize

namespace ActualRule5Caller
open RMAF Universal233 OrdinaryDispatch OrdinaryDispatch.BudgetOptimization

/-- Correctness of the unchanged finite optimizer from exact ordinary queries.
No old whole-solver or optimizer correctness theorem is invoked. -/
theorem optimizer_of_query_exact (T S : Tree)
    (proper : DepthOne.proper T S = true)
    (queries : ∀ q, QueryExact T S q (FastOrdinary.solve q T S)) :
    ∃ q F o,
      (optimize T S).search.selected = some (q,F) ∧
      (optimize T S).search.trials = failedTrials 0 q ++ [(q,some F)] ∧
      (optimize T S).output = some o ∧
      (optimize T S).recoveries = [(F,some o)] ∧
      FastOrdinary.solve q T S = some F ∧ FinalCutRecovery.recover S F = some o ∧
      agreement T S F = true ∧ agreement T S o.partition = true ∧
      CutRealization.RealizedOutput S o ∧
      o.sourceCuts.Nodup ∧ (∀ e ∈ o.sourceCuts, CoreGraph.Valid S e ∧ e ≠ []) ∧
      o.sourceCuts.length = q ∧ o.partition.length = q + 1 ∧
      (∀ G, agreement T S G = true → o.partition.length ≤ G.length) ∧
      q < (leaves T).length := by
  obtain ⟨x,hx⟩ := IndependentReconstruction.leaf_witness T
  have positive : 0 < (leaves T).length := by
    apply List.length_pos_iff.mpr
    intro empty
    simp only [empty,List.not_mem_nil] at hx
  have witness := singletons_agreement T S proper
  obtain ⟨H,success⟩ := FastOrdinary.query_complete
    (queries ((leaves T).length - 1)) (singletons (leaves T)) witness
    (by simp [singletons])
  obtain ⟨q,F,selected⟩ := scan_complete (fun q => FastOrdinary.solve q T S)
    (leaves T).length 0 ((leaves T).length - 1) (by omega) (by omega) ⟨H,success⟩
  obtain ⟨sk,offset,upper,trials,found,failed⟩ :=
    scan_success (fun q => FastOrdinary.solve q T S) (leaves T).length 0 q F selected
  have skq : sk = q := by omega
  subst sk
  have valid : agreement T S F = true ∧ F.length - 1 ≤ q ∧
      ∀ G, agreement T S G = true → F.length ≤ G.length := by
    simpa only [found,QueryExact] using queries q
  have fpos := FastOrdinary.original_positive valid.1
  have tight : F.length - 1 = q := by
    by_cases smaller : F.length - 1 < q
    · have no := failed (F.length - 1) (by omega) smaller
      have impossible : F.length - 1 < F.length - 1 := by
        exact (show ∀ G, agreement T S G = true → F.length - 1 < G.length - 1 from
          by simpa only [no,QueryExact] using queries (F.length - 1)) F valid.1
      omega
    · omega
  have len : F.length = q + 1 := by omega
  have ns := ((DepthOne.proper_iff T S).mp proper).2.1
  obtain ⟨o,recovered,oaf,cuts,parts,realized,_⟩ :=
    FinalCutRecovery.recover_original_agreement T S F ns valid.1
  have edges := FinalCutRecovery.recover_edges S F o recovered
  refine ⟨q,F,o,?_,?_,?_,?_,found,recovered,valid.1,oaf,realized,
    edges.1,edges.2,?_,?_,?_,upper⟩
  · simp only [optimize,proper,ite_true,finish_search,selected]
  · simpa only [optimize,proper,ite_true,finish_search] using trials
  · simp only [optimize,proper,ite_true,finish,selected,recovered]
  · simp only [optimize,proper,ite_true,finish,selected,recovered]
  · omega
  · omega
  · intro G hG
    rw [parts]
    exact valid.2.2 G hG

#print axioms optimizer_of_query_exact
end ActualRule5Caller
