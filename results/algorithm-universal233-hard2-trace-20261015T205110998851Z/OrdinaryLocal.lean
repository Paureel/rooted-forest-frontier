import CallbackLocality
namespace Universal233.BothBadLocal
open RMAF CoreProgram ForestState RestrictionBridge SourceCoverage BothBad ForestMinCompletion

/-- ExactAt for the actual forest program at a bounded query, on all states. -/
theorem forest_exact_at_local (actual : Ordinary) (K : Nat) (localIH : LocalOrdinaryIH K actual)
 (T : Option Tree) (ss : List Tree) (b : Nat) (low : b≤K) :
 BothBad.ExactAt (GenericForest.solve actual) T ss b := by
 have exactness := GenericForest.LocalIH.exact_at_budget_bound K actual localIH
 refine ⟨?_,?_⟩
 · intro H answer
   have sound := exactness.1 T ss b H low answer
   refine ⟨sound.1,sound.2,?_⟩
   intro F hF
   by_cases budget : additionalCost ss F≤b
   · obtain ⟨G,hG,len⟩ := exactness.2 T ss b F low hF budget
     have eq : G=H := Option.some.inj (hG.symm.trans answer)
     rw [eq] at len
     exact Nat.sub_le_sub_right len ss.length
   · omega
 · intro F hF budget
   obtain ⟨H,hH,len⟩ := exactness.2 T ss b F low hF budget
   exact ⟨H,hH⟩

/-- Global exactness is used only for an erased completed callback in proofs. -/
theorem completed_forest_exact (completed : Ordinary) (IH : GenericForest.OrdinaryIH completed) :
 ExactSolverHyp (GenericForest.solve completed) := by
 intro T ss b proper
 have localIH : LocalOrdinaryIH b completed :=
  ⟨fun t s k F _ hp hF=>IH.sound t s k F hp hF,
   fun t s k G _ hp hG budget=>IH.complete t s k G hp hG budget⟩
 exact forest_exact_at_local completed b localIH T ss b (Nat.le_refl _)

theorem ordinary_candidate_local (actual : Ordinary) (T S : Tree) (Q : Forest) (b : Nat) (F : Forest)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (hQ : partitionCheck (leaves S) Q=true) (eS : pairwiseEmbeddings S Q=true)
 (eT : pairwiseEmbeddings T Q=true)
 (hF : agreement T S F=true) (href : Refines F Q) (budget : F.length-Q.length≤b)
 (localIH : LocalOrdinaryIH b actual) :
 ∃H,(ordinaryExecution (GenericForest.solve actual) T S Q b).answer=some H ∧
 agreement T S H=true ∧ Refines H Q ∧ H.length-Q.length≤b ∧ H.length≤F.length := by
 obtain ⟨completed,IH,equal⟩ := ordinaryIH_extension localIH
 obtain ⟨H,answer,agree,refine,bound,len⟩ := global_ordinary_candidate (GenericForest.solve completed) T S Q b F
  hs ht hQ eS eT hF href budget (completed_forest_exact completed IH)
 have programs : ∀T ss r,r≤b → GenericForest.solve completed T ss r=GenericForest.solve actual T ss r := by
  intro T ss r hr
  exact GenericForest.LocalIH.solve_congr_budget completed actual r
   (fun t s k hk=>equal t s k (Nat.le_trans hk hr)) T ss
 have answers := ordinaryExecution_answer_congr_at (GenericForest.solve completed) (GenericForest.solve actual)
  b programs T S Q b (Nat.le_refl _)
 exact ⟨H,answers.symm.trans answer,agree,refine,bound,len⟩

theorem ordinary_candidate_below (actual : Ordinary) (q : Nat) (IH : BelowIH q actual)
 (T S : Tree) (Q : Forest) (b : Nat) (low : b<q) (F : Forest)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (hQ : partitionCheck (leaves S) Q=true) (eS : pairwiseEmbeddings S Q=true)
 (eT : pairwiseEmbeddings T Q=true)
 (hF : agreement T S F=true) (href : Refines F Q) (budget : F.length-Q.length≤b) :
 ∃H,(ordinaryExecution (GenericForest.solve actual) T S Q b).answer=some H ∧
 agreement T S H=true ∧ Refines H Q ∧ H.length-Q.length≤b ∧ H.length≤F.length :=
 ordinary_candidate_local actual T S Q b F hs ht hQ eS eT hF href budget (IH b low)

/-- Even q=0 is supported. The empty low-budget range constrains no callback. -/
theorem below_ordinary_extension {q : Nat} {actual : Ordinary} (IH : BelowIH q actual) :
 ∃completed,GenericForest.OrdinaryIH completed ∧ ∀t s b,b<q → completed t s b=actual t s b := by
 cases q with
 | zero =>
  refine ⟨minimumCallback,⟨?_,?_⟩,?_⟩
  · intro t s b F hp answer
    exact minimumCallback_sound answer
  · intro t s b G hp agree budget
    exact minimumCallback_complete agree budget
  · intro t s b low
    omega
 | succ K =>
  obtain ⟨completed,global,equal⟩ := ordinaryIH_extension (IH K (by omega))
  exact ⟨completed,global,fun t s b low=>equal t s b (by omega)⟩

theorem forest_programs_congr_below (f g : Ordinary) (q : Nat)
 (equal : ∀t s b,b<q → f t s b=g t s b) :
 ∀T ss b,b<q → GenericForest.solve f T ss b=GenericForest.solve g T ss b := by
 intro T ss b low
 exact GenericForest.LocalIH.solve_congr_budget f g b (fun t s r hr=>equal t s r (by omega)) T ss
end Universal233.BothBadLocal
