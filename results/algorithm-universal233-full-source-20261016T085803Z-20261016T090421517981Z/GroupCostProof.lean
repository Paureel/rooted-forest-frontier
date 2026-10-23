import GroupReverseProof
namespace ForestGroups
open RMAF RestrictionBridge ForestState

theorem source_blocks_balance (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees T ss F = true) :
    (ss.map (fun s => (family (leaves s) F).length - 1)).sum + ss.length = F.length := by
  obtain ⟨hp,hF,href,hE,hS⟩ := agrees_parts T ss F ha
  have hsp := (proper_parts _ _ hp).2
  have hr : Refines F (ss.map leaves) := by
    intro B hb
    obtain ⟨s,hs,hBs⟩ := href B hb
    exact ⟨leaves s,List.mem_map.2 ⟨s,hs,rfl⟩,hBs⟩
  have he := total_family_length (labels T) F (ss.map leaves) hF hsp hr
  have hb := sum_sub_one (ss.map leaves) (fun U => (family U F).length) (by
    intro U hu
    exact List.length_pos_iff.2 (family_nonempty (labels T) F (ss.map leaves) hF hsp hr U hu))
  simp only [List.map_map,List.length_map,Function.comp_def] at he hb
  omega

theorem sources_le_blocks (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees T ss F = true) : ss.length ≤ F.length := by
  have := source_blocks_balance T ss F ha
  omega

theorem sum_sub_balance {α : Type} (Q : List α) (f g : α → Nat)
    (hle : ∀ U ∈ Q, g U ≤ f U) :
    (Q.map (fun U => f U - g U)).sum + (Q.map g).sum = (Q.map f).sum := by
  induction Q with
  | nil => simp
  | cons U Q ih =>
    have hu := hle U (by simp)
    have hi := ih (fun V hv => hle V (by simp [hv]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem source_group_lengths (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (hp : proper T ss = true) (hq : partitionCheck (labels T) Q = true)
    (own : Owns ss Q) : (Q.map (fun U => (owned ss U).length)).sum = ss.length := by
  have href : Refines (ss.map leaves) Q := by
    intro B hB
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hB
    exact own s hs
  have he := total_family_length (labels T) (ss.map leaves) Q (proper_parts _ _ hp).2 hq href
  have hc : Q.map (fun U => (owned ss U).length) = Q.map (fun U => (family U (ss.map leaves)).length) := by
    apply List.map_congr_left
    intro U hU
    rw [←owned_leaves,List.length_map]
  simpa only [hc,List.length_map] using he

/-- Natural subtraction is exact: every valid local forest has at least as many
blocks as its current literal source trees. No truncation is hidden in the sum. -/
theorem forward_exact_cost (T : Option Tree) (ss : List Tree) (Q F : List (List Nat))
    (ha : agrees T ss F = true) (hq : partitionCheck (labels T) Q = true)
    (own : Owns ss Q) :
    (Q.map (fun U => additionalCost (owned ss U) (family U F))).sum = additionalCost ss F := by
  have hp := (agrees_parts T ss F ha).1
  have hF := (agrees_parts T ss F ha).2.1
  have hg := source_group_lengths T ss Q hp hq own
  have hf := total_family_length (labels T) F Q hF hq (state_refines T ss F Q ha own)
  have hb := sum_sub_balance Q (fun U => (family U F).length) (fun U => (owned ss U).length)
    (fun U hu => sources_le_blocks _ _ _ (local_forward T ss Q F ha hq own U hu))
  simp only [additionalCost]
  omega

theorem reverse_exact_cost (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (hp : proper T ss = true)
    (hq : partitionCheck (labels T) Q = true) (own : Owns ss Q)
    (ha : ∀ U ∈ Q, agrees (localTarget T U) (owned ss U) (G U) = true) :
    (Q.map (fun U => additionalCost (owned ss U) (G U))).sum = additionalCost ss (Q.flatMap G) := by
  have hs := source_group_lengths T ss Q hp hq own
  have hb := sum_sub_balance Q (fun U => (G U).length) (fun U => (owned ss U).length)
    (fun U hu => sources_le_blocks _ _ _ (ha U hu))
  simp only [additionalCost,List.length_flatMap]
  omega

theorem forward_every_budget (T : Option Tree) (ss : List Tree) (Q F : List (List Nat))
    (ha : agrees T ss F = true) (hq : partitionCheck (labels T) Q = true)
    (own : Owns ss Q) (q : Nat) :
    additionalCost ss F ≤ q ↔
      (Q.map (fun U => additionalCost (owned ss U) (family U F))).sum ≤ q := by
  rw [forward_exact_cost T ss Q F ha hq own]

theorem reverse_every_budget (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (hp : proper T ss = true)
    (hq : partitionCheck (labels T) Q = true) (own : Owns ss Q)
    (cross : CrossClear T ss Q)
    (ha : ∀ U ∈ Q, agrees (localTarget T U) (owned ss U) (G U) = true)
    (q : Nat) :
    agrees T ss (Q.flatMap G) = true ∧
    (additionalCost ss (Q.flatMap G) ≤ q ↔
      (Q.map (fun U => additionalCost (owned ss U) (G U))).sum ≤ q) := by
  refine ⟨reverse_reconstruction T ss Q G hp hq own cross ha,?_⟩
  rw [reverse_exact_cost T ss Q G hp hq own ha]
end ForestGroups
