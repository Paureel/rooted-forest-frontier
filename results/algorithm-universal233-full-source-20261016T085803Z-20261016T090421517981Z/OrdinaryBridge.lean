import ForestContract
namespace Universal233.BothBad
open RMAF CoreProgram ForestState RestrictionBridge MafScheduler

theorem nat_minimum_from (P : Nat → Prop) (n : Nat) (hn : P n) :
    ∃ m, P m ∧ ∀ r, P r → m≤r := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hs : ∃ m, m<n ∧ P m
    · obtain ⟨m,hm,hP⟩ := hs
      exact ih m hm hP
    · refine ⟨n,hn,?_⟩
      intro r hr
      by_cases hle : n≤r
      · exact hle
      · exact False.elim (hs ⟨r,by omega,hr⟩)

theorem local_minimum_exists (t s : Tree) (F : Forest) (hF : agreement t s F=true) :
    ∃ m, LocalMinimum t s m := by
  obtain ⟨m,⟨H,hH,hcost⟩,hmin⟩ := nat_minimum_from
    (fun m => ∃ H, agreement t s H=true ∧ H.length-1=m) (F.length-1) ⟨F,hF,rfl⟩
  exact ⟨m,⟨H,hH,hcost⟩,fun G hG => hmin _ ⟨G,hG,rfl⟩⟩

theorem single_state_proper (t s : Tree) (hp : DepthOne.proper t s=true) :
    proper (some t) [s]=true := by
  obtain ⟨ht,hs,hperm⟩ := (DepthOne.proper_iff t s).1 hp
  simp only [proper,labels,Bool.and_eq_true,List.map_cons,List.map_nil]
  exact ⟨decide_eq_true ht,(partition_labels_congr _ _ [leaves s] (fun x => hperm.mem_iff)).2
    (OutputState.full_partition (leaves s) hs (leaves_nonempty s))⟩

theorem exact_local_sound (solve : ForestSolver) (t s : Tree) (m b : Nat)
    (hp : proper (some t) [s]=true) (hm : LocalMinimum t s m)
    (IH : ExactAt solve (some t) [s] b) (H : Forest)
    (hH : asTree solve t s b=some H) :
    agreement t s H=true ∧ H.length-1=m ∧ m≤b := by
  obtain ⟨hstate,hbudget,hminimal⟩ := IH.1 H hH
  have ha := (initial_state_agreement_iff t s H hp).1 hstate
  obtain ⟨G,hG,hcost⟩ := hm.1
  have gstate := (initial_state_agreement_iff t s G hp).2 hG
  have hlow := hm.2 H ha
  have hhigh := hminimal G gstate
  simp only [additionalCost,List.length_singleton] at hbudget hhigh
  exact ⟨ha,by omega,by omega⟩

theorem exact_local_complete (solve : ForestSolver) (t s : Tree) (m b : Nat)
    (hp : proper (some t) [s]=true) (hm : LocalMinimum t s m)
    (IH : ExactAt solve (some t) [s] b) (hb : m≤b) :
    ∃ H, asTree solve t s b=some H := by
  obtain ⟨F,hF,hcost⟩ := hm.1
  apply IH.2 F ((initial_state_agreement_iff t s F hp).2 hF)
  simpa only [additionalCost,List.length_singleton,hcost] using hb

/-- Proof-only restricted trees and minima are derived from a given original
agreement. They are not inputs to the executable MAF scheduler. -/
theorem ordinary_candidate (solve : ForestSolver) (T S : Tree) (Q : Forest) (b : Nat) (F : Forest)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (hQ : partitionCheck (leaves S) Q=true) (eS : pairwiseEmbeddings S Q=true)
    (eT : pairwiseEmbeddings T Q=true)
    (hF : agreement T S F=true) (href : Refines F Q) (hbudget : F.length-Q.length≤b)
    (IH : ∀ U∈Q, ∀ t s, restrict U T=some t → restrict U S=some s →
      ∀ k, ExactAt solve (some t) [s] k) :
    ∃ H, (ordinaryExecution solve T S Q b).answer=some H ∧
      agreement T S H=true ∧ Refines H Q ∧ H.length-Q.length≤b ∧ H.length≤F.length := by
  classical
  obtain ⟨locals,hcost⟩ := forward_decomposition T S F Q ht hs hF hQ href
  let t : List Nat → Tree := fun U => (restrict U T).getD (.leaf 0)
  let s : List Nat → Tree := fun U => (restrict U S).getD (.leaf 0)
  have rt : ∀ U∈Q, restrict U T=some (t U) := by
    intro U hU
    obtain ⟨tu,su,htu,hsu,_⟩ := locals U hU
    simp [t,htu]
  have rs : ∀ U∈Q, restrict U S=some (s U) := by
    intro U hU
    obtain ⟨tu,su,htu,hsu,_⟩ := locals U hU
    simp [s,hsu]
  have localAF : ∀ U∈Q, agreement (t U) (s U) (family U F)=true :=
    fun U hU => forward_local T S (t U) (s U) F Q U hF hQ href hU (rt U hU) (rs U hU)
  let m : List Nat → Nat := fun U => if h : ∃ k, LocalMinimum (t U) (s U) k then Classical.choose h else 0
  have hm : ∀ U∈Q, LocalMinimum (t U) (s U) (m U) := by
    intro U hU
    have he := local_minimum_exists (t U) (s U) _ (localAF U hU)
    simpa only [m,dite_eq_left he] using Classical.choose_spec he
  have partT : partitionCheck (leaves T) Q=true := by
    have hFA := hF
    simp only [agreement,Bool.and_eq_true] at hFA
    exact (partition_labels_congr _ _ Q
      (checked_labels_iff _ _ F hFA.1.1.1.1 hFA.1.1.1.2)).2 hQ
  have properLocal := checked_block_proper T S Q ht hs partT hQ t s rt rs
  have hsound : ∀ U∈Q, ∀ k H, asTree solve (t U) (s U) k=some H →
      agreement (t U) (s U) H=true ∧ H.length-1=m U ∧ m U≤k := by
    intro U hU k H hH
    exact exact_local_sound solve (t U) (s U) (m U) k
      (single_state_proper _ _ (properLocal U hU).2) (hm U hU)
      (IH U hU _ _ (rt U hU) (rs U hU) k) H hH
  have hcomplete : ∀ U∈Q, ∀ k, m U≤k → ∃ H, asTree solve (t U) (s U) k=some H := by
    intro U hU k hk
    exact exact_local_complete solve (t U) (s U) (m U) k
      (single_state_proper _ _ (properLocal U hU).2) (hm U hU)
      (IH U hU _ _ (rt U hU) (rs U hU) k) hk
  obtain ⟨H,hH⟩ := disjoint_caller_complete T S Q ht hs partT hQ t s m rt rs hm
    (asTree solve) hsound hcomplete b F hF href hbudget
  obtain ⟨hAF,hRef,hEq,hb⟩ := disjoint_caller_sound T S Q ht hs partT hQ eT eS t s m rt rs hm
    (asTree solve) hsound b H hH
  have hmin := original_minimum_lower T S Q ht hs hQ t s m rt rs hm F hF href
  have fstate := OutputState.original_to_state T S Q F ht hs
    (by intro x;have hh:=hF;simp only [agreement,Bool.and_eq_true] at hh;exact checked_labels_iff _ _ F hh.1.1.1.1 hh.1.1.1.2 x)
    hQ hF href
  have hfLen := ForestGroups.sources_le_blocks _ _ _ fstate
  rw [(OutputState.checked_materialization S Q hs hQ).1] at hfLen
  exact ⟨H,(ordinaryExecution_value solve T S Q b).trans hH,hAF,hRef,hb,by omega⟩
end Universal233.BothBad
