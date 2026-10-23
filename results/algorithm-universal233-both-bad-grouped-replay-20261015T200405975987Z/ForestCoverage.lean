import ForestPermutation
namespace ForestPretest01
open RMAF RestrictionBridge ForestState ForestGroups
open Universal233

theorem source_small_complete (s : Tree) (F : Forest)
    (hn : (leaves s).Nodup) (hp : partitionCheck (leaves s) F = true)
    (he : pairwiseEmbeddings s F = true) (hc : F.length-1 ≤ 1) :
    ∃ c ∈ DepthOne.candidates s, ForestPerm F (DepthOne.forest s c) ∧
      DepthOne.cutCost c = F.length-1 := by
  have hne : F ≠ [] := by
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves s) (RestrictionBridge.leaves_nonempty s)
    obtain ⟨B,hB,_⟩ := checked_covers (leaves s) F hp hx
    intro hz; simp [hz] at hB
  have hl : F.length ≤ 2 := by omega
  cases F with
  | nil => exact False.elim (hne rfl)
  | cons A F =>
    cases F with
    | nil =>
      have hA : A.Perm (leaves s) := by simpa using DepthOne.checked_flatten_perm _ _ hn hp
      exact ⟨none,by simp [DepthOne.candidates],.cons hA .nil,by simp [DepthOne.cutCost]⟩
    | cons B F =>
      have hz : F = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hl; omega)
      subst F
      obtain ⟨p,hpedge,hAB⟩ := DepthOne.source_two_split s A B hn hp he
      refine ⟨some p,by simp [DepthOne.candidates,hpedge],?_,by simp [DepthOne.cutCost]⟩
      rcases hAB with hA | hB
      · have hB := DepthOne.complement_perm s A B p hn hp hA
        exact .cons hA.symm (.cons hB.symm .nil)
      · have swap : ForestPerm [A,B] [B,A] := .outer (List.Perm.swap B A [])
        have hps : partitionCheck (leaves s) [B,A] = true := by rw [←partition_perm _ _ _ swap]; exact hp
        have hA := DepthOne.complement_perm s B A p hn hps hB
        exact swap.trans (.cons hB.symm (.cons hA.symm .nil))

theorem candidate_zero (ss : List Tree) (F : Forest) (hm : F ∈ candidates ss)
    (hc : additionalCost ss F = 0) : F = unchanged ss := by
  rcases List.mem_cons.1 hm with he | hcut
  · exact he
  · have hl := oneCuts_length ss F hcut
    simp only [additionalCost] at hc
    omega

theorem assemble_small (ss : List Tree) (out : Tree → Forest)
    (locals : ∀ s ∈ ss, ∃ c ∈ DepthOne.candidates s,
      ForestPerm (out s) (DepthOne.forest s c) ∧ DepthOne.cutCost c = (out s).length-1)
    (hc : (ss.map (fun s => (out s).length-1)).sum ≤ 1) :
    ∃ G ∈ candidates ss, ForestPerm (ss.flatMap out) G ∧
      additionalCost ss G = (ss.map (fun s => (out s).length-1)).sum := by
  induction ss with
  | nil => exact ⟨[],by simp [candidates,unchanged],.nil,rfl⟩
  | cons s ss ih =>
    have hsum : (out s).length-1 + (ss.map (fun r => (out r).length-1)).sum ≤ 1 := by simpa using hc
    obtain ⟨c,hc,hperm,hcost⟩ := locals s (by simp)
    obtain ⟨G,hG,hGP,hGC⟩ := ih (fun r hr => locals r (by simp [hr])) (by omega)
    cases c with
    | none =>
      have he : DepthOne.cutCost none = 0 := rfl
      have hzero : (out s).length-1 = 0 := hcost.symm.trans he
      refine ⟨leaves s :: G,?_,?_,?_⟩
      · rcases List.mem_cons.1 hG with rfl | hG
        · simp [candidates,unchanged]
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨G,hG,rfl⟩))
      · exact hperm.append hGP
      · simpa [additionalCost,hzero] using hGC
    | some p =>
      have hone : (out s).length-1 = 1 := hcost.symm
      have hzero : additionalCost ss G = 0 := by omega
      have hGe := candidate_zero ss G hG hzero
      have hp : p ∈ DepthOne.edges s := by simpa [DepthOne.candidates] using hc
      refine ⟨DepthOne.forest s (some p) ++ unchanged ss,?_,?_,?_⟩
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨p,hp,rfl⟩))
      · simpa [hGe] using hperm.append hGP
      · have hz : (ss.map (fun r => (out r).length-1)).sum = 0 := by omega
        simp [additionalCost,DepthOne.forest,unchanged,hone,hz]

/-- Regroup by the unique original-source owner; no target-clearance premise. -/
theorem regroup_perm (L : List Nat) (F Q : Forest)
    (hF : partitionCheck L F = true) (hQ : partitionCheck L Q = true)
    (href : Refines F Q) : F.Perm (Q.flatMap (family · F)) := by
  apply List.perm_iff_count.2
  intro B
  by_cases hB : B ∈ F
  · have hone := one_parent_count L F Q hF hQ href B hB
    rw [List.count_flatMap]
    have hmap : Q.map (List.count B ∘ (family · F)) =
        Q.map (fun U => if contained B U then F.count B else 0) := by
      apply List.map_congr_left
      intro U hU
      simp only [Function.comp_def,family]
      by_cases hb : contained B U = true
      · simp only [hb,↓reduceIte]
        exact List.count_filter (p := fun C => contained C U) hb
      · have hf : contained B U = false := by cases h : contained B U <;> simp_all
        simp only [hf,Bool.false_eq_true,↓reduceIte]
        apply List.count_eq_zero.2
        simp [hf]
    rw [hmap]
    have sum (Q : Forest) : (Q.map (fun U => if contained B U then F.count B else 0)).sum =
        F.count B * Q.countP (contained B ·) := by
      induction Q with
      | nil => simp
      | cons U Q ih =>
        cases hb : contained B U <;>
          simp only [List.map_cons,List.sum_cons,List.countP_cons,hb,Bool.false_eq_true,
            ↓reduceIte,ih,Nat.mul_zero,Nat.mul_one,Nat.mul_add,Nat.zero_add,Nat.add_comm]
    rw [sum,hone,Nat.mul_one]
  · have hz : F.count B = 0 := List.count_eq_zero.2 hB
    rw [hz]
    symm
    apply List.count_eq_zero.2
    intro hb
    obtain ⟨U,_,hU⟩ := List.mem_flatMap.1 hb
    exact hB ((mem_family _ _ _).1 hU).1

/-- Every actual cost≤1 AF, with arbitrary labels and block order, is represented
by an unchanged/full-current-forest original-edge candidate. -/
theorem universal_coverage (T : Option Tree) (ss : List Tree) (F : Forest)
    (ha : agrees T ss F = true) (hc : additionalCost ss F ≤ 1) :
    ∃ G ∈ candidates ss, ForestPerm F G ∧ agrees T ss G = true ∧
      additionalCost ss G = additionalCost ss F := by
  obtain ⟨hp,hF,own,ht,hS⟩ := agrees_parts T ss F ha
  have hQ := (proper_parts T ss hp).2
  have href : Refines F (ss.map leaves) := by
    intro B hB
    obtain ⟨s,hs,hBs⟩ := own B hB
    exact ⟨leaves s,List.mem_map.2 ⟨s,hs,rfl⟩,hBs⟩
  have balance := source_blocks_balance T ss F ha
  have hsum : (ss.map (fun s => (family (leaves s) F).length-1)).sum = additionalCost ss F := by
    simp only [additionalCost]; omega
  have localSmall (s : Tree) (hs : s ∈ ss) : (family (leaves s) F).length-1 ≤ 1 := by
    have hle := GenericForest.member_le_sum
      (ss.map (fun r => (family (leaves r) F).length-1)) _ (List.mem_map.2 ⟨s,hs,rfl⟩)
    omega
  have localComplete (s : Tree) (hs : s ∈ ss) : ∃ c ∈ DepthOne.candidates s,
      ForestPerm (family (leaves s) F) (DepthOne.forest s c) ∧
      DepthOne.cutCost c = (family (leaves s) F).length-1 := by
    have hcheck := hS s hs
    simp only [sourceCheck,Bool.and_eq_true] at hcheck
    have hn : (leaves s).Nodup := ForestState.checked_block_nodup _ _ hQ _ (List.mem_map.2 ⟨s,hs,rfl⟩)
    exact source_small_complete s _ hn hcheck.1.1 hcheck.2 (localSmall s hs)
  obtain ⟨G,hG,hperm,hcost⟩ := assemble_small ss (fun s => family (leaves s) F) localComplete (by omega)
  have hreg : F.Perm (ss.flatMap (fun s => family (leaves s) F)) := by
    simpa only [List.flatMap_map,Function.comp_def] using regroup_perm (labels T) F (ss.map leaves) hF hQ href
  have full : ForestPerm F G := (ForestPerm.outer hreg).trans hperm
  exact ⟨G,hG,full,by rw [←agrees_perm T ss F G full]; exact ha,hcost.trans hsum⟩

end ForestPretest01
