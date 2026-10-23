import Reconstruction01

namespace Universal233.DepthOne
open RMAF CoreGraph CutRealization RestrictionBridge Integration

theorem agreement_single_perm (T S : Tree) (A B : List Nat) (h : A.Perm B) :
    agreement T S [A] = agreement T S [B] := by
  have hn : A.isEmpty = B.isEmpty := by cases A <;> cases B <;> simp_all
  have hc : ∀ L, partitionCheck L [A] = partitionCheck L [B] := by
    intro L
    simp only [partitionCheck,List.all_cons,List.all_nil,Bool.and_true,
      List.flatten_cons,List.flatten_nil,List.append_nil]
    rw [hn,h.all_eq]
    have hh := List.all_congr (l₁ := L) rfl (fun x => congrArg (fun n : Nat => n == 1) (h.count_eq x))
    rw [hh]
  simp only [agreement,hc,restrictionAgrees,restrict_members T A B (fun _ => h.mem_iff),
    restrict_members S A B (fun _ => h.mem_iff),pairwiseEmbeddings,List.all_cons,List.all_nil,Bool.and_true]

theorem agreement_nonempty (T S : Tree) (F : List (List Nat))
    (ha : agreement T S F = true) : F ≠ [] := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves S) (CutRealization.leaves_nonempty S)
  obtain ⟨B,hB,_⟩ := checked_covers (leaves S) F hh.1.1.1.2 hx
  intro he
  simp [he] at hB

/-- Completeness quantifies over every literal original agreement partition,
including arbitrary block order and arbitrary original natural-number labels. -/
theorem candidate_complete (T S : Tree) (F : List (List Nat))
    (hn : (leaves S).Nodup) (ha : agreement T S F = true) (hcost : F.length - 1 ≤ 1) :
    ∃ c, c ∈ candidates S ∧ agreement T S (forest S c) = true ∧ cutCost c ≤ F.length - 1 := by
  have hne := agreement_nonempty T S F ha
  have hlen : F.length ≤ 2 := by omega
  cases F with
  | nil => exact False.elim (hne rfl)
  | cons A F =>
    cases F with
    | nil =>
      have hh := ha
      simp only [agreement,Bool.and_eq_true] at hh
      have hperm : A.Perm (leaves S) := by simpa using checked_flatten_perm _ _ hn hh.1.1.1.2
      refine ⟨none,by simp [candidates],?_,by simp [cutCost]⟩
      rw [forest,←agreement_single_perm T S A (leaves S) hperm]
      exact ha
    | cons B F =>
      have hF : F = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hlen; omega)
      subst F
      obtain ⟨p,hp,hpa⟩ := two_block_complete T S A B hn ha
      exact ⟨some p,by simp [candidates,hp],hpa,by simp [cutCost]⟩

@[simp] theorem proper_iff (T S : Tree) : proper T S = true ↔
    (leaves T).Nodup ∧ (leaves S).Nodup ∧ (leaves T).Perm (leaves S) := by
  simp only [proper,Bool.and_eq_true,decide_eq_true_eq]
  exact and_assoc

theorem found_spec (T S : Tree) (c : Option Vertex) (h : pretest01 T S = .found c) :
    proper T S = true ∧ c ∈ candidates S ∧ agreement T S (forest S c) = true ∧
      ∀ d, d ∈ candidates S → agreement T S (forest S d) = true → cutCost c ≤ cutCost d := by
  unfold pretest01 at h
  split at h
  · rename_i hp
    cases hb : best cutCost (fun d => agreement T S (forest S d)) (candidates S) with
    | none => simp [hb] at h
    | some d =>
      have he : d = c := by simpa [hb] using h
      subst d
      exact ⟨hp,best_spec _ _ _ c hb⟩
  · simp at h

theorem cutCost_le_one (c : Option Vertex) : cutCost c ≤ 1 := by cases c <;> simp [cutCost]

/-- An actual returned partition is globally minimum among all original
agreement partitions, not merely among the enumerated candidates. -/
theorem found_globally_minimum (T S : Tree) (c : Option Vertex)
    (h : pretest01 T S = .found c) :
    agreement T S (forest S c) = true ∧
    (forest S c).length - 1 = cutCost c ∧
    ∀ F, agreement T S F = true → cutCost c ≤ F.length - 1 := by
  obtain ⟨hp,hc,ha,hmin⟩ := found_spec T S c h
  refine ⟨ha,by cases c <;> simp [forest,cutCost],?_⟩
  intro F hF
  by_cases hsmall : F.length - 1 ≤ 1
  · obtain ⟨d,hd,hda,hbound⟩ := candidate_complete T S F ((proper_iff T S).1 hp).2.1 hF hsmall
    exact Nat.le_trans (hmin d hd hda) hbound
  · have := cutCost_le_one c
    omega

theorem rejected_spec (T S : Tree) (h : pretest01 T S = .rejected) :
    proper T S = true ∧ ∀ c, c ∈ candidates S → agreement T S (forest S c) = false := by
  unfold pretest01 at h
  split at h
  · rename_i hp
    cases hb : best cutCost (fun c => agreement T S (forest S c)) (candidates S) with
    | none => exact ⟨hp,(best_none_iff _ _ _).1 hb⟩
    | some c => simp [hb] at h
  · simp at h

/-- Failure on a proper pair excludes every original agreement of cost 0 or 1. -/
theorem rejected_lower_bound (T S : Tree) (h : pretest01 T S = .rejected) :
    ∀ F, agreement T S F = true → 2 ≤ F.length - 1 := by
  obtain ⟨hp,hnone⟩ := rejected_spec T S h
  intro F hF
  by_cases hsmall : F.length - 1 ≤ 1
  · obtain ⟨c,hc,hca,hbound⟩ := candidate_complete T S F ((proper_iff T S).1 hp).2.1 hF hsmall
    have hf := hnone c hc
    simp [hf] at hca
  · omega

theorem pretest_complete (T S : Tree) (hp : proper T S = true)
    (F : List (List Nat)) (ha : agreement T S F = true) (hcost : F.length - 1 ≤ 1) :
    ∃ c, pretest01 T S = .found c ∧ agreement T S (forest S c) = true ∧ cutCost c ≤ F.length - 1 := by
  obtain ⟨d,hd,hda,hbound⟩ := candidate_complete T S F ((proper_iff T S).1 hp).2.1 ha hcost
  obtain ⟨c,hc⟩ := best_exists cutCost (fun c => agreement T S (forest S c)) (candidates S) d hd hda
  have hfound : pretest01 T S = .found c := by simp [pretest01,hp,hc]
  have hspec := found_spec T S c hfound
  exact ⟨c,hfound,hspec.2.2.1,Nat.le_trans (hspec.2.2.2 d hd hda) hbound⟩

theorem refused_iff (T S : Tree) : pretest01 T S = .refused ↔ proper T S = false := by
  unfold pretest01
  cases hp : proper T S <;> simp [hp]
  cases best cutCost (fun c => agreement T S (forest S c)) (candidates S) <;> simp

end Universal233.DepthOne
