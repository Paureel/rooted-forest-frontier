import LowerBound
import GroupCost

namespace AllGoodDP
open RMAF RestrictionBridge ForestState

-- The completed restriction cost lemmas count every current source component.
-- This derives the offset balance from literal partition/refinement checks.
theorem sources_le_blocks (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees T ss F = true) : ss.length ≤ F.length := by
  have hs := agrees_parts T ss F ha
  have hQ := (proper_parts T ss hs.1).2
  have href : Refines F (ss.map leaves) := by
    intro B hB
    obtain ⟨s,hsm,hBs⟩ := hs.2.2.1 B hB
    exact ⟨leaves s,List.mem_map.2 ⟨s,hsm,rfl⟩,hBs⟩
  have he := total_family_length (labels T) F (ss.map leaves) hs.2.1 hQ href
  have hb := sum_sub_one (ss.map leaves) (fun U => (family U F).length) (by
    intro U hU
    exact List.length_pos_iff.2 (family_nonempty (labels T) F (ss.map leaves)
      hs.2.1 hQ href U hU))
  simp only [List.length_map] at hb
  omega

theorem additional_exact (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees T ss F = true) : additionalCost ss F + ss.length = F.length := by
  exact Nat.sub_add_cancel (sources_le_blocks T ss F ha)

theorem agreement_nonempty (t : Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees (some t) ss F = true) : 0 < F.length := by
  have hF := (agrees_parts (some t) ss F ha).2.1
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ (RestrictionBridge.leaves_nonempty t)
  obtain ⟨B,hB,_⟩ := checked_covers (leaves t) F hF hx
  exact List.length_pos_iff.2 (List.ne_nil_of_mem hB)

theorem candidate_blocks_minimum (t : Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees (some t) ss F = true) : (candidate (some t) ss).length ≤ F.length := by
  have hp := (agrees_parts (some t) ss F ha).1
  obtain ⟨p,hpvalid,hpcost⟩ := agreement_coloring t ss F ha
  have hmin := (actual_paint_spec t ss hp).2 p hpvalid
  have hblocks := candidate_count_bound t ss
  have hpos := agreement_nonempty t ss F ha
  omega

theorem candidate_minimum (T : Option Tree) (ss : List Tree) (hg : allGood T ss = true) :
    agrees T ss (candidate T ss) = true ∧
    ∀ F, agrees T ss F = true → additionalCost ss (candidate T ss) ≤ additionalCost ss F := by
  refine ⟨candidate_agrees T ss hg,?_⟩
  intro F ha
  cases T with
  | none => simp [candidate,additionalCost]
  | some t => exact Nat.sub_le_sub_right (candidate_blocks_minimum t ss F ha) ss.length

theorem candidate_no_leafless (t : Tree) (ss : List Tree)
    (hg : allGood (some t) ss = true) :
    ∀ B ∈ rawBlocks (solve (List.range ss.length) (owner ss) t), B ≠ [] := by
  have ha := candidate_agrees (some t) ss hg
  have hp := (allGood_parts (some t) ss hg).1
  obtain ⟨p,hpvalid,hpcost⟩ := agreement_coloring t ss (candidate (some t) ss) ha
  have hmin := (actual_paint_spec t ss hp).2 p hpvalid
  have hblocks := candidate_count_bound t ss
  have hpos := agreement_nonempty t ss (candidate (some t) ss) ha
  have hlen : (candidate (some t) ss).length =
      (rawBlocks (solve (List.range ss.length) (owner ss) t)).length := by
    rw [raw_length]
    omega
  have hfilter : ∀ B ∈ rawBlocks (solve (List.range ss.length) (owner ss) t), !B.isEmpty :=
    List.length_filter_eq_length_iff.1 hlen
  intro B hB
  simpa using hfilter B hB

def decideBudget (T : Option Tree) (ss : List Tree) (q : Nat) : Bool :=
  (run T ss).any (fun F => decide (additionalCost ss F ≤ q))

theorem decideBudget_correct (T : Option Tree) (ss : List Tree) (q : Nat)
    (hg : allGood T ss = true) :
    decideBudget T ss q = true ↔ ∃ F, agrees T ss F = true ∧ additionalCost ss F ≤ q := by
  have hm := candidate_minimum T ss hg
  simp only [decideBudget,run,hg,ite_true,Option.any_some,decide_eq_true_eq]
  constructor
  · intro hq; exact ⟨candidate T ss,hm.1,hq⟩
  · rintro ⟨F,ha,hq⟩
    exact Nat.le_trans (hm.2 F ha) hq

theorem run_total_exact (T : Option Tree) (ss : List Tree) (hg : allGood T ss = true) :
    ∃ F, run T ss = some F ∧ agrees T ss F = true ∧
      additionalCost ss F + ss.length = F.length ∧
      ∀ G, agrees T ss G = true → additionalCost ss F ≤ additionalCost ss G := by
  have hm := candidate_minimum T ss hg
  exact ⟨candidate T ss,by simp [run,hg],hm.1,additional_exact T ss _ hm.1,hm.2⟩

end AllGoodDP
