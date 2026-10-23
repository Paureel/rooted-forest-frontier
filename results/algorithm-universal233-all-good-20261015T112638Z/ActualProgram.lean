import ColorRegions

namespace AllGoodDP
open RMAF RestrictionBridge ForestState

def owner (ss : List Tree) (x : Nat) : Nat :=
  ss.findIdx (fun s => (leaves s).contains x)

def allGood (T : Option Tree) (ss : List Tree) : Bool :=
  proper T ss && ss.all (fun s => targetAgrees T s (leaves s))

-- This is an executable candidate, not yet a certified ForestState solver.
-- Its first missing graph theorem is recorded at this exact call below.
def candidate (T : Option Tree) (ss : List Tree) : List (List Nat) :=
  match T with
  | none => []
  | some t => blocks (solve (List.range ss.length) (owner ss) t)

def run (T : Option Tree) (ss : List Tree) : Option (List (List Nat)) :=
  if allGood T ss then some (candidate T ss) else none

theorem allGood_parts (T : Option Tree) (ss : List Tree) (h : allGood T ss = true) :
    proper T ss = true ∧ ∀ s ∈ ss, targetAgrees T s (leaves s) = true := by
  simpa only [allGood,Bool.and_eq_true,List.all_eq_true] using h

theorem proper_parts (T : Option Tree) (ss : List Tree) (hp : proper T ss = true) :
    (labels T).Nodup ∧ partitionCheck (labels T) (ss.map leaves) = true := by
  simpa [proper] using hp

theorem owner_lt (T : Option Tree) (ss : List Tree) (hp : proper T ss = true)
    (x : Nat) (hx : x ∈ labels T) : owner ss x < ss.length := by
  have hpart := (proper_parts T ss hp).2
  obtain ⟨U,hU,hxU⟩ := checked_covers (labels T) (ss.map leaves) hpart hx
  obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hU
  exact List.findIdx_lt_length_of_exists ⟨s,hs,List.contains_iff_mem.2 hxU⟩

theorem owner_index (ss : List Tree) (x : Nat) (h : owner ss x < ss.length) :
    x ∈ leaves ss[owner ss x] := by
  have hh : (leaves ss[owner ss x]).contains x = true :=
    List.findIdx_getElem (w := h)
  exact List.contains_iff_mem.1 hh

theorem some_sources_nonempty (t : Tree) (ss : List Tree)
    (hp : proper (some t) ss = true) : ss ≠ [] := by
  have hn := leaves_nonempty t
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ hn
  have := owner_lt (some t) ss hp x hx
  intro he
  simp [he] at this

theorem actual_paint_spec (t : Tree) (ss : List Tree)
    (hp : proper (some t) ss = true) :
    Valid (List.range ss.length) (owner ss) t
      (solve (List.range ss.length) (owner ss) t) ∧
    ∀ p, Valid (List.range ss.length) (owner ss) t p →
      changes (solve (List.range ss.length) (owner ss) t) ≤ changes p := by
  apply solve_spec
  · have hn := some_sources_nonempty t ss hp
    have hl := List.length_pos_iff.2 hn
    simp only [ne_eq,List.range_eq_nil]
    omega
  · intro x hx
    exact List.mem_range.2 (owner_lt (some t) ss hp x hx)

theorem candidate_partition (T : Option Tree) (ss : List Tree)
    (hp : proper T ss = true) : partitionCheck (labels T) (candidate T ss) = true := by
  cases T with
  | none => rfl
  | some t =>
    have hv := (actual_paint_spec t ss hp).1
    have he := valid_erase hv
    have hn := (proper_parts (some t) ss hp).1
    have hcheck := blocks_partition _ (he.symm ▸ hn)
    rw [he] at hcheck
    exact hcheck

theorem candidate_ownership (T : Option Tree) (ss : List Tree)
    (hp : proper T ss = true) :
    ∀ B ∈ candidate T ss, ∃ s ∈ ss, B ⊆ leaves s := by
  cases T with
  | none => simp [candidate]
  | some t =>
    have hv := (actual_paint_spec t ss hp).1
    intro B hB
    obtain ⟨c,hc,hm⟩ := blocks_mono hv B hB
    have hcl := List.mem_range.1 hc
    refine ⟨ss[c],List.getElem_mem hcl,?_⟩
    intro x hx
    have hxc := hm x hx
    have hix : owner ss x < ss.length := by omega
    have hi := owner_index ss x hix
    simpa only [hxc] using hi

theorem candidate_count_bound (t : Tree) (ss : List Tree) :
    (candidate (some t) ss).length ≤
      changes (solve (List.range ss.length) (owner ss) t) + 1 := blocks_length _

theorem actual_raw_count (t : Tree) (ss : List Tree) :
    (rawBlocks (solve (List.range ss.length) (owner ss) t)).length =
      changes (solve (List.range ss.length) (owner ss) t) + 1 := raw_length _

theorem none_agreement (ss : List Tree) (hp : proper none ss = true) :
    ss = [] ∧ agrees none ss (candidate none ss) = true ∧
      additionalCost ss (candidate none ss) = 0 := by
  have hpart := (proper_parts none ss hp).2
  have he : ss = [] := by
    cases ss with
    | nil => rfl
    | cons s ss =>
      have hn := leaves_nonempty s
      obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ hn
      have hf := checked_label [] ((s :: ss).map leaves) hpart
        (List.mem_map.2 ⟨s,by simp,rfl⟩) hx
      simp at hf
  subst ss
  exact ⟨rfl,rfl,rfl⟩

-- StateSoundness.candidate_agrees proves every literal checker conjunct.
-- Exact minimum over all state agreements is a separate lower-bound target.

end AllGoodDP
