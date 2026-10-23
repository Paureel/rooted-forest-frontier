import GroupStateFacts
import GroupReconstruction

/-! Literal current source grouping. A group may contain target-overlapping source
pieces. No original-parent target-hull or cut-edge union hypothesis occurs. -/
namespace ForestGroups
open RMAF RestrictionBridge ForestState

def localTarget (T : Option Tree) (U : List Nat) : Option Tree := T.bind (restrict U)
def owned (ss : List Tree) (U : List Nat) : List Tree := ss.filter (fun s => contained (leaves s) U)
def Owns (ss : List Tree) (Q : List (List Nat)) : Prop :=
  ∀ s ∈ ss, ∃ U ∈ Q, leaves s ⊆ U

def CrossClear (T : Option Tree) (ss : List Tree) (Q : List (List Nat)) : Prop :=
  ∀ t, T = some t → ∀ U ∈ Q, ∀ V ∈ Q, U ≠ V →
  ∀ s ∈ owned ss U, ∀ r ∈ owned ss V,
    Clear (minimalVertices (leaves s) t) (minimalVertices (leaves r) t)

@[simp] theorem mem_owned (s : Tree) (ss : List Tree) (U : List Nat) :
    s ∈ owned ss U ↔ s ∈ ss ∧ leaves s ⊆ U := by simp [owned]

theorem owned_leaves (ss : List Tree) (U : List Nat) :
    (owned ss U).map leaves = family U (ss.map leaves) := by
  simp only [owned,family,List.filter_map,Function.comp_def]

theorem checked_empty (F : List (List Nat)) (h : partitionCheck [] F = true) : F = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro B hB
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B (checked_nonempty [] F h B hB)
  have := checked_label [] F h hB hx
  simp at this

theorem group_unique (L : List Nat) (Q : List (List Nat))
    (hq : partitionCheck L Q = true) (U V : List Nat) (hU : U ∈ Q) (hV : V ∈ Q)
    (x : Nat) (hxU : x ∈ U) (hxV : x ∈ V) : U = V := by
  obtain ⟨W,hW,hxW,hcW,one⟩ := unique_label_owner Q x
    (checked_count L Q hq (checked_label L Q hq hU hxU))
  exact (one U hU hxU).trans (one V hV hxV).symm

theorem block_group_owner (L : List Nat) (Q : List (List Nat))
    (hq : partitionCheck L Q = true) (U V B : List Nat)
    (hU : U ∈ Q) (hV : V ∈ Q) (hn : B ≠ []) (hBU : B ⊆ U) (hBV : B ⊆ V) : U = V := by
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B hn
  exact group_unique L Q hq U V hU hV x (hBU hx) (hBV hx)

theorem state_refines (T : Option Tree) (ss : List Tree) (F Q : List (List Nat))
    (ha : agrees T ss F = true) (own : Owns ss Q) : Refines F Q := by
  intro B hB
  obtain ⟨s,hs,hBs⟩ := (agrees_parts T ss F ha).2.2.1 B hB
  obtain ⟨U,hU,hsU⟩ := own s hs
  exact ⟨U,hU,List.Subset.trans hBs hsU⟩

theorem group_target (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (hp : proper T ss = true) (hq : partitionCheck (labels T) Q = true)
    (U : List Nat) (hU : U ∈ Q) :
    ∃ t u, T = some t ∧ restrict U t = some u ∧ localTarget T U = some u ∧
      (leaves u).Perm U := by
  have hn := checked_nonempty (labels T) Q hq U hU
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil U hn
  have hxl := checked_label (labels T) Q hq hU hx
  cases T with
  | none => simp [labels] at hxl
  | some t =>
    obtain ⟨u,hu⟩ := restriction_exists t U ⟨x,hxl,hx⟩
    exact ⟨t,u,rfl,hu,hu,component_labels t u U Q hu (proper_parts _ _ hp).1 hq hU⟩

theorem local_proper (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (hp : proper T ss = true) (hq : partitionCheck (labels T) Q = true)
    (own : Owns ss Q) (U : List Nat) (hU : U ∈ Q) :
    proper (localTarget T U) (owned ss U) = true := by
  obtain ⟨t,u,ht,hu,he,hperm⟩ := group_target T ss Q hp hq U hU
  subst T
  have hsp := (proper_parts _ _ hp).2
  have href : Refines (ss.map leaves) Q := by
    intro B hB
    obtain ⟨s,hs,rfl⟩ := List.mem_map.1 hB
    exact own s hs
  have hpart := local_partition t u U (ss.map leaves) Q hu hsp hq href hU
  simp only [proper,he,labels,Bool.and_eq_true,decide_eq_true_eq,owned_leaves]
  exact ⟨restricted_nodup t u U hu (proper_parts _ _ hp).1,hpart⟩

theorem family_nested (S U : List Nat) (F : List (List Nat)) (hSU : S ⊆ U) :
    family S (family U F) = family S F := by
  simp only [family,List.filter_filter]
  apply List.filter_congr
  intro B hB
  by_cases hb : B ⊆ S
  · have hu := List.Subset.trans hb hSU
    simp [(contained_iff B S).2 hb,(contained_iff B U).2 hu]
  · have hf : contained B S = false := by cases h : contained B S <;> simp_all
    simp [hf]

end ForestGroups
