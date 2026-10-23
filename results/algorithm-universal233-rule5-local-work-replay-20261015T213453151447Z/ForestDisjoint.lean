import ForestDisjointPlan
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups
open Universal233 Universal233.PaidQueries Universal233.MafScheduler

theorem disjoint_exact_of_ordinary (ordinary : Tree → Tree → Nat → Option Forest)
    (ho : OrdinaryIH ordinary) : DisjointExact ordinary := by
  classical
  intro t ss q G ha hclear hq
  have hp := (agrees_parts _ _ _ ha).1
  let keys := ss.map (pair t)
  have pproper (p : Tree × Tree) (hpk : p ∈ keys) : DepthOne.proper p.1 p.2 = true := by
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hpk
    exact (pair_actual t ss hp s hs).2.2
  have existsMin (p : Tree × Tree) (hpk : p ∈ keys) : ∃ n, LocalMinimum p.1 p.2 n := by
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hpk
    have hg := local_pair_forward t ss G ha s hs
    obtain ⟨F,hF⟩ := ho.complete _ _ ((family (leaves s) G).length-1) _
      (pair_actual t ss hp s hs).2.2 hg (Nat.le_refl _)
    obtain ⟨hf,hb,hminimal⟩ := ho.sound _ _ _ F (pair_actual t ss hp s hs).2.2 hF
    exact ⟨F.length-1,⟨F,hf,rfl⟩,fun H hH => by have := hminimal H hH; omega⟩
  let m : Tree × Tree → Nat := fun p => if h : ∃ n, LocalMinimum p.1 p.2 n then h.choose else 0
  have hm (p : Tree × Tree) (hpk : p ∈ keys) : LocalMinimum p.1 p.2 (m p) := by
    have he := existsMin p hpk
    simpa only [m,dite_eq_left he] using he.choose_spec
  obtain ⟨js,hjobs,hkeys,hplan⟩ := jobs_planned t ss m
    (fun s hs => (pair_actual t ss hp s hs).1)
    (fun s hs => (pair_actual t ss hp s hs).2.2)
    (fun s hs => hm (pair t s) (List.mem_map.2 ⟨s,hs,rfl⟩))
  have jk : ∀ j ∈ js, j.problem ∈ keys := by
    intro j hj
    change j.problem ∈ ss.map (pair t)
    rw [←hkeys]
    exact List.mem_map.2 ⟨j,hj,rfl⟩
  let recPair : Tree × Tree → Nat → Option (Nat × Forest) :=
    fun p b => (ordinary p.1 p.2 b).map (fun F => (F.length-1,F))
  have recSound : ∀ p ∈ keys, ∀ b c F, recPair p b = some (c,F) → c = m p ∧ PairValid m p F := by
    intro p hpk b c F hh
    obtain ⟨H,hH,he⟩ := Option.map_eq_some_iff.1 hh
    have hh' := Prod.mk.inj he
    have hHF : H = F := hh'.2
    subst H
    obtain ⟨hag,hbudget,hmin⟩ := ho.sound _ _ _ F (pproper p hpk) hH
    have hlow := (hm p hpk).2 F hag
    obtain ⟨K,hK,hKm⟩ := (hm p hpk).1
    have hupp := hmin K hK
    have heq : F.length-1 = m p := by omega
    exact ⟨by omega,⟨hag,heq⟩⟩
  have recComplete : ∀ p ∈ keys, ∀ b, m p ≤ b → ∃ x, recPair p b = some x := by
    intro p hpk b hb
    obtain ⟨K,hK,hKm⟩ := (hm p hpk).1
    obtain ⟨F,hF⟩ := ho.complete _ _ b K (pproper p hpk) hK (by omega)
    exact ⟨(F.length-1,F),by simp [recPair,hF]⟩
  have totalEq : totalMinimum m js = (ss.map (fun s => m (pair t s))).sum := by
    rw [totalMinimum_keys,hkeys,List.map_map]
    rfl
  have totalLe : totalMinimum m js ≤ additionalCost ss G := by
    have hle := sum_map_le' ss (fun s => m (pair t s)) (fun s => (family (leaves s) G).length-1)
      (fun s hs => (hm (pair t s) (List.mem_map.2 ⟨s,hs,rfl⟩)).2 _ (local_pair_forward t ss G ha s hs))
    have hbal := source_blocks_balance _ _ _ ha
    simp only [additionalCost]
    rw [totalEq]
    omega
  obtain ⟨xs,hxs⟩ := schedule_complete_on m (PairValid m) recPair keys recSound recComplete
    q js hplan jk (Nat.le_trans totalLe hq)
  obtain ⟨hans,hansCost,haccepted⟩ := schedule_sound_on m (PairValid m) recPair keys recSound
    q js hplan jk xs hxs
  have keysND : (js.map Job.problem).Nodup := by
    rw [hkeys]
    apply List.Pairwise.map (R := fun s r : Tree => s ≠ r) (pair t) (fun s r h he => h (congrArg Prod.snd he))
    exact proper_sources_nodup t ss hp
  obtain ⟨f,hf,hvalid⟩ := answers_indexed m (PairValid m) js xs hans keysND
  have each (s : Tree) (hs : s ∈ ss) : PairValid m (pair t s) (f (pair t s)).2 := by
    have hpk : pair t s ∈ js.map Job.problem := by rw [hkeys]; exact List.mem_map.2 ⟨s,hs,rfl⟩
    obtain ⟨j,hj,hjp⟩ := List.mem_map.1 hpk
    simpa [hjp] using (hvalid j hj).2
  let out : Tree → Forest := fun s => (f (pair t s)).2
  obtain ⟨hstate,hcost⟩ := local_assemble t ss hp hclear out (fun s hs => (each s hs).1)
  have flatEq : xs.flatMap Prod.snd = ss.flatMap out := by
    rw [←hf,hkeys,List.map_map,List.flatMap_map]
    rfl
  have sumEq : (ss.map (fun s => (out s).length-1)).sum = totalMinimum m js := by
    rw [totalEq]
    congr 1
    apply List.map_congr_left
    intro s hs
    exact (each s hs).2
  have hfinalCost : additionalCost ss (xs.flatMap Prod.snd) = totalMinimum m js := by
    rw [flatEq,hcost,sumEq]
  have finalState : agrees (some t) ss (xs.flatMap Prod.snd) = true := by simpa only [flatEq] using hstate
  have ac : accepted (some t) ss q (xs.flatMap Prod.snd) = true := by
    simp only [accepted,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨finalState,by omega⟩
  refine ⟨xs.flatMap Prod.snd,?_,?_⟩
  · simp only [disjointSolve,disjointAttempt,hjobs,Option.map_some,Option.bind_some]
    change (schedule recPair q js).answers.bind (fun ys => checked (some t) ss q (ys.flatMap Prod.snd)) = _
    simp [hxs,checked,ac]
  · have hlen := sources_le_blocks _ _ _ finalState
    have hlenG := sources_le_blocks _ _ _ ha
    simp only [additionalCost] at hfinalCost totalLe
    omega

/-- Conditional only on the printed future ordinary-tree exact-minimum IH.
All generic source-forest geometry, replacement and paid assembly are local. -/
theorem exact_of_ordinary (ordinary : Tree → Tree → Nat → Option Forest)
    (ho : OrdinaryIH ordinary) : ExactAt (solve ordinary) :=
  conditional_exact ordinary ho (disjoint_exact_of_ordinary ordinary ho)

end GenericForest
