import GroupPartition

namespace RestrictionBridge
open RMAF

theorem sum_map_add_nat {α : Type} (L : List α) (f g : α → Nat) :
    (L.map (fun x => f x + g x)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem sum_indicator {α : Type} (L : List α) (p : α → Bool) :
    (L.map (fun x => if p x then 1 else 0)).sum = L.countP p := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons,List.sum_cons,List.countP_cons,ih]; omega

theorem family_cons_length (U B : List Nat) (F : List (List Nat)) :
    (family U (B :: F)).length = (family U F).length + if contained B U then 1 else 0 := by
  cases hb : contained B U <;> simp [family,hb]

theorem distribute_family_lengths (Q F : List (List Nat)) :
    (Q.map (fun U => (family U F).length)).sum =
      (F.map (fun B => Q.countP (contained B ·))).sum := by
  induction F with
  | nil => induction Q <;> simp_all [family]
  | cons B F ih =>
    simp only [List.map_cons,List.sum_cons]
    have he : (Q.map (fun U => (family U (B :: F)).length)) =
        Q.map (fun U => (family U F).length + if contained B U then 1 else 0) := by
      apply List.map_congr_left
      intro U hu
      exact family_cons_length U B F
    rw [he,sum_map_add_nat,sum_indicator,ih]
    exact Nat.add_comm _ _

theorem one_parent_count (labels : List Nat) (F Q : List (List Nat))
    (hF : partitionCheck labels F = true) (hQ : partitionCheck labels Q = true)
    (href : Refines F Q) (B : List Nat) (hB : B ∈ F) :
    Q.countP (contained B ·) = 1 := by
  have hn := checked_nonempty labels F hF B hB
  obtain ⟨x,hx⟩ : ∃ x, x ∈ B := List.exists_mem_of_ne_nil B hn
  have hxl := checked_label labels F hF hB hx
  obtain ⟨U,hU,hxU,hcU,unique⟩ := unique_label_owner Q x (checked_count labels Q hQ hxl)
  obtain ⟨V,hV,hBV⟩ := href B hB
  have hvu := unique V hV (hBV hx)
  have hBU : B ⊆ U := by simpa [hvu] using hBV
  have he : Q.countP (contained B ·) = Q.countP (· == U) := by
    apply List.countP_congr
    intro W hW
    simp only [contained_iff,beq_iff_eq]
    constructor
    · intro hBW; exact unique W hW (hBW hx)
    · intro he; simpa [he] using hBU
  rw [he]
  exact hcU

theorem total_family_length (labels : List Nat) (F Q : List (List Nat))
    (hF : partitionCheck labels F = true) (hQ : partitionCheck labels Q = true)
    (href : Refines F Q) :
    (Q.map (fun U => (family U F).length)).sum = F.length := by
  rw [distribute_family_lengths]
  have hm : F.map (fun B => Q.countP (contained B ·)) = F.map (fun _ => 1) := by
    apply List.map_congr_left
    intro B hB
    exact one_parent_count labels F Q hF hQ href B hB
  rw [hm]
  have ho : ∀ L : List (List Nat), (L.map (fun _ => 1)).sum = L.length := by
    intro L
    induction L with
    | nil => simp
    | cons B L ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; omega
  exact ho F

theorem family_nonempty (labels : List Nat) (F Q : List (List Nat))
    (hF : partitionCheck labels F = true) (hQ : partitionCheck labels Q = true)
    (href : Refines F Q) (U : List Nat) (hU : U ∈ Q) : family U F ≠ [] := by
  have hn := checked_nonempty labels Q hQ U hU
  obtain ⟨x,hx⟩ : ∃ x, x ∈ U := List.exists_mem_of_ne_nil U hn
  have hxl := checked_label labels Q hQ hU hx
  obtain ⟨B,hB,hxB⟩ := checked_covers labels F hF hxl
  obtain ⟨V,hV,hBV⟩ := href B hB
  obtain ⟨W,hW,hxW,hcW,unique⟩ := unique_label_owner Q x (checked_count labels Q hQ hxl)
  have heU := unique U hU hx
  have heV := unique V hV (hBV hxB)
  have hBU : B ⊆ U := by simpa [heU,heV] using hBV
  have hm : B ∈ family U F := (mem_family B U F).2 ⟨hB,hBU⟩
  intro he
  rw [he] at hm
  simp at hm

theorem sum_sub_one (Q : List (List Nat)) (n : List Nat → Nat)
    (positive : ∀ U ∈ Q, 0 < n U) :
    (Q.map (fun U => n U - 1)).sum + Q.length = (Q.map n).sum := by
  induction Q with
  | nil => simp
  | cons U Q ih =>
    have hp := positive U (by simp)
    have ht : ∀ V ∈ Q, 0 < n V := fun V hv => positive V (by simp [hv])
    have hi := ih ht
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem exact_cost (labels : List Nat) (F Q : List (List Nat))
    (hF : partitionCheck labels F = true) (hQ : partitionCheck labels Q = true)
    (href : Refines F Q) :
    (Q.map (fun U => (family U F).length - 1)).sum = F.length - Q.length := by
  have positive : ∀ U ∈ Q, 0 < (family U F).length := by
    intro U hU
    exact List.length_pos_iff.2 (family_nonempty labels F Q hF hQ href U hU)
  have hs := sum_sub_one Q (fun U => (family U F).length) positive
  have ht := total_family_length labels F Q hF hQ href
  omega

end RestrictionBridge
