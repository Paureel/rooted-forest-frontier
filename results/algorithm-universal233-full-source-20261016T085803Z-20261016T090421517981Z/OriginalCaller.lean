import OriginalReconstruction

namespace Universal233.MafScheduler
open RMAF PaidQueries RestrictionBridge

theorem sum_map_le {P : Type} (Q : List P) (f g : P → Nat)
    (h : ∀ U∈Q, f U≤g U) : (Q.map f).sum≤(Q.map g).sum := by
  induction Q with
  | nil => simp
  | cons U Q ih =>
    have hh := h U (by simp)
    have ht := ih (fun V hv => h V (by simp [hv]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem original_minimum_lower (T S : Tree) (Q : Forest)
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQS : partitionCheck (leaves S) Q=true) (t s : List Nat → Tree) (m : List Nat → Nat)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U))
    (hm : ∀ U∈Q, LocalMinimum (t U) (s U) (m U))
    (F : Forest) (hF : agreement T S F=true) (href : Refines F Q) :
    (Q.map m).sum≤F.length-Q.length := by
  have hdecomp := forward_decomposition T S F Q pt ps hF hQS href
  have hle : (Q.map m).sum≤(Q.map (fun U => (family U F).length-1)).sum := by
    apply sum_map_le
    intro U hU
    exact (hm U hU).2 _ (forward_local T S (t U) (s U) F Q U hF hQS href hU (ht U hU) (hs U hU))
  omega

/-- The recursive solver hypotheses are explicit and concern only literal
    restricted local pairs. The implementation constructs its slots itself
    from the actual depth01 pretest and concatenates returned local forests. -/
theorem disjoint_caller_sound (T S : Tree) (Q : Forest)
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (eT : pairwiseEmbeddings T Q=true) (eS : pairwiseEmbeddings S Q=true)
    (t s : List Nat → Tree) (m : List Nat → Nat)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U))
    (hm : ∀ U∈Q, LocalMinimum (t U) (s U) (m U))
    (solve : Tree → Tree → Nat → Option Forest)
    (hsolve : ∀ U∈Q, ∀ b F, solve (t U) (s U) b=some F →
      agreement (t U) (s U) F=true ∧ F.length-1=m U ∧ m U≤b)
    (q : Nat) (F : Forest) (hret : solveDisjoint T S solve q Q=some F) :
    agreement T S F=true ∧ Refines F Q ∧ F.length-Q.length=(Q.map m).sum ∧
      F.length-Q.length≤q := by
  obtain ⟨js,hprep,hkeys,hplan⟩ := prepare_planned T S Q t s m ht hs
    (checked_block_proper T S Q pt ps hQT hQS t s ht hs) hm
  have hk : ∀ j∈js, j.problem∈Q := by
    intro j hj; rw [←hkeys]; exact List.mem_map.2 ⟨j,hj,rfl⟩
  have hsrec := recursive_sound T S Q t s m solve ht hs
    (fun U hU b G hG => ⟨(hsolve U hU b G hG).1,(hsolve U hU b G hG).2.1⟩)
  have hh : (schedule (recursive T S solve) q js).answers.map (fun xs => xs.flatMap Prod.snd)=some F := by
    simpa [solveDisjoint,attempt,hprep] using hret
  cases he : (schedule (recursive T S solve) q js).answers with
  | none => simp [he] at hh
  | some xs =>
    have hF : xs.flatMap Prod.snd=F := by simpa [he] using hh
    subst F
    obtain ⟨ha,hcost,hq⟩ := schedule_sound_on m (LocalValid t s m) (recursive T S solve) Q
      hsrec q js hplan hk xs he
    obtain ⟨hag,hadd,href⟩ := answers_original_reconstruction T S Q pt ps hQT hQS eT eS t s m ht hs js xs hkeys ha
    have htmin : totalMinimum m js=(Q.map m).sum := by rw [totalMinimum_keys,hkeys]
    exact ⟨hag,href,by omega,by omega⟩

theorem disjoint_caller_complete (T S : Tree) (Q : Forest)
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (t s : List Nat → Tree) (m : List Nat → Nat)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U))
    (hm : ∀ U∈Q, LocalMinimum (t U) (s U) (m U))
    (solve : Tree → Tree → Nat → Option Forest)
    (hsound : ∀ U∈Q, ∀ b F, solve (t U) (s U) b=some F →
      agreement (t U) (s U) F=true ∧ F.length-1=m U ∧ m U≤b)
    (hcomplete : ∀ U∈Q, ∀ b, m U≤b → ∃ F, solve (t U) (s U) b=some F)
    (q : Nat) (F : Forest) (hF : agreement T S F=true) (href : Refines F Q)
    (hq : F.length-Q.length≤q) : ∃ G, solveDisjoint T S solve q Q=some G := by
  obtain ⟨js,hprep,hkeys,hplan⟩ := prepare_planned T S Q t s m ht hs
    (checked_block_proper T S Q pt ps hQT hQS t s ht hs) hm
  have hk : ∀ j∈js, j.problem∈Q := by
    intro j hj; rw [←hkeys]; exact List.mem_map.2 ⟨j,hj,rfl⟩
  have hsrec := recursive_sound T S Q t s m solve ht hs
    (fun U hU b G hG => ⟨(hsound U hU b G hG).1,(hsound U hU b G hG).2.1⟩)
  have hcrec := recursive_complete T S Q t s m solve ht hs hcomplete
  have hmin := original_minimum_lower T S Q pt ps hQS t s m ht hs hm F hF href
  have htmin : totalMinimum m js=(Q.map m).sum := by rw [totalMinimum_keys,hkeys]
  obtain ⟨xs,hxs⟩ := schedule_complete_on m (LocalValid t s m) (recursive T S solve) Q
    hsrec hcrec q js hplan hk (by omega)
  exact ⟨xs.flatMap Prod.snd,by simp [solveDisjoint,attempt,hprep,hxs]⟩
end Universal233.MafScheduler
