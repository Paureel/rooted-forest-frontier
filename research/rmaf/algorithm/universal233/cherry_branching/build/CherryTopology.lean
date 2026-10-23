import CherryGraph

namespace ForestState
open RMAF RestrictionBridge

theorem rootedIso_refl (t : Tree) : RootedIso t t := (sameShape_correct t t).1 (sameShape_refl t)

theorem rootedIso_symm {t u : Tree} (h : RootedIso t u) : RootedIso u t := by
  induction h with
  | leaf x => exact RootedIso.leaf x
  | straight h1 h2 ih1 ih2 => exact RootedIso.straight ih1 ih2
  | swapped h1 h2 ih1 ih2 => exact RootedIso.swapped ih2 ih1

theorem rootedIso_trans {t u v : Tree} (h : RootedIso t u) (g : RootedIso u v) : RootedIso t v := by
  induction h generalizing v with
  | leaf x => cases g; exact RootedIso.leaf x
  | straight h1 h2 ih1 ih2 =>
    cases g with
    | straight g1 g2 => exact RootedIso.straight (ih1 g1) (ih2 g2)
    | swapped g1 g2 => exact RootedIso.swapped (ih1 g1) (ih2 g2)
  | swapped h1 h2 ih1 ih2 =>
    cases g with
    | straight g1 g2 => exact RootedIso.swapped (ih1 g2) (ih2 g1)
    | swapped g1 g2 => exact RootedIso.straight (ih1 g2) (ih2 g1)

def OptionIso (x y : Option Tree) : Prop :=
  match x,y with
  | none,none => True
  | some t,some u => RootedIso t u
  | _,_ => False

theorem optionIso_refl (x : Option Tree) : OptionIso x x := by
  cases x with
  | none => trivial
  | some t => exact rootedIso_refl t

theorem optionIso_join (l r l' r' : Option Tree) (hl : OptionIso l l') (hr : OptionIso r r') :
    OptionIso (join l r) (join l' r') := by
  cases l <;> cases l' <;> cases r <;> cases r' <;>
    simp_all [OptionIso,join]
  exact RootedIso.straight hl hr

theorem expand_preserves_iso (a b z : Nat) {t u : Tree} (h : RootedIso t u) :
    RootedIso (expand a b z t) (expand a b z u) := by
  induction h with
  | leaf x => exact rootedIso_refl _
  | straight h1 h2 ih1 ih2 => exact RootedIso.straight ih1 ih2
  | swapped h1 h2 ih1 ih2 => exact RootedIso.swapped ih1 ih2

theorem expand_join (a b z : Nat) (l r : Option Tree) :
    (join l r).map (expand a b z) = join (l.map (expand a b z)) (r.map (expand a b z)) := by
  cases l <;> cases r <;> rfl

theorem expand_absent (a b z : Nat) (t : Tree) (hz : z ∉ leaves t) : expand a b z t = t := by
  induction t with
  | leaf x =>
    have hn : x ≠ z := by simpa [leaves,eq_comm] using hz
    simp [expand,hn]
  | node l r hl hr =>
    have hzl : z ∉ leaves l := fun hx => hz (by simp [leaves,hx])
    have hzr : z ∉ leaves r := fun hx => hz (by simp [leaves,hx])
    simp [expand,hl hzl,hr hzr]

theorem expand_restrict_absent (a b z : Nat) (t : Tree) (B : List Nat)
    (hz : z ∉ leaves t) : (restrict B t).map (expand a b z) = restrict B t := by
  cases hr : restrict B t with
  | none => rfl
  | some u =>
    have hzu : z ∉ leaves u := by
      intro hx
      exact hz ((restricted_labels_exact t u B hr).1 hx).1
    simp [expand_absent a b z u hzu]

theorem restrict_mask_equal (t : Tree) (B C : List Nat)
    (mask : ∀ x ∈ leaves t, B.contains x = C.contains x) : restrict B t = restrict C t := by
  induction t with
  | leaf x => simp only [restrict,mask x (by simp [leaves])]
  | node l r hl hr =>
    rw [restrict_node,restrict_node,hl (fun x hx => mask x (by simp [leaves,hx])),
      hr (fun x hx => mask x (by simp [leaves,hx]))]

theorem restrict_add_absent (t : Tree) (B : List Nat) (b : Nat) (hb : b ∉ leaves t) :
    restrict (b :: B) t = restrict B t := by
  apply restrict_mask_equal
  intro x hx
  have hn : x ≠ b := by intro he; subst x; exact hb hx
  simp [hn]

theorem nodup_append_avoid_right (l r : Tree) (x : Nat)
    (nd : (leaves (.node l r)).Nodup) (hx : x ∈ leaves l) : x ∉ leaves r := by
  intro hy
  have hc := List.nodup_iff_count.1 nd x
  have hp := List.count_pos_iff.2 hx
  have hq := List.count_pos_iff.2 hy
  simp only [leaves,List.count_append] at hc
  omega

theorem nodup_append_avoid_left (l r : Tree) (x : Nat)
    (nd : (leaves (.node l r)).Nodup) (hx : x ∈ leaves r) : x ∉ leaves l := by
  intro hy
  exact nodup_append_avoid_right l r x nd hy hx

theorem CherryAt.restriction_expand_iso {t : Tree} {a b : Nat} {w : Vertex}
    (h : CherryAt a b t w) (B : List Nat) (nd : (leaves t).Nodup)
    (ha : a ∈ B) (hb : b ∉ B) :
    OptionIso ((restrict B t).map (expand a b a)) (restrict (b :: B) t) := by
  induction h with
  | straight =>
    have hne : a ≠ b := by intro he; subst b; exact hb ha
    simpa [restrict,ha,hb,expand,Ne.symm hne,OptionIso] using rootedIso_refl (.node (.leaf a) (.leaf b))
  | swapped =>
    have hne : a ≠ b := by intro he; subst b; exact hb ha
    simpa [restrict,ha,hb,expand,Ne.symm hne,OptionIso] using
      (RootedIso.swapped (RootedIso.leaf a) (RootedIso.leaf b) :
        RootedIso (.node (.leaf a) (.leaf b)) (.node (.leaf b) (.leaf a)))
  | @left l r w h ih =>
    have ndl : (leaves l).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nar := nodup_append_avoid_right l r a nd h.labels.1
    have nbr := nodup_append_avoid_right l r b nd h.labels.2
    rw [restrict_node,restrict_node,expand_join]
    apply optionIso_join
    · exact ih ndl
    · rw [expand_restrict_absent a b a r B nar,restrict_add_absent r B b nbr]
      exact optionIso_refl _
  | @right l r w h ih =>
    have ndr : (leaves r).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nal := nodup_append_avoid_left l r a nd h.labels.1
    have nbl := nodup_append_avoid_left l r b nd h.labels.2
    rw [restrict_node,restrict_node,expand_join]
    apply optionIso_join
    · rw [expand_restrict_absent a b a l B nal,restrict_add_absent l B b nbl]
      exact optionIso_refl _
    · exact ih ndr

theorem synchronized_endpoint_reassignment_topology (T S : Tree) (a b : Nat)
    (B : List Nat) (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (chT : cherry a b T = true) (chS : cherry a b S = true)
    (ha : a ∈ B) (hb : b ∉ B) (h : restrictionAgrees T S B = true) :
    restrictionAgrees T S (b :: B) = true := by
  obtain ⟨w,hw⟩ := cherry_at_exists T a b chT
  obtain ⟨v,hv⟩ := cherry_at_exists S a b chS
  have it := hw.restriction_expand_iso B ndT ha hb
  have is := hv.restriction_expand_iso B ndS ha hb
  cases rt : restrict B T with
  | none => simp [restrictionAgrees,rt] at h
  | some t =>
    cases rs : restrict B S with
    | none => simp [restrictionAgrees,rs] at h
    | some s =>
      have iso : RootedIso t s := (sameShape_correct t s).1 (by simpa [restrictionAgrees,rt,rs] using h)
      rw [rt] at it
      rw [rs] at is
      cases et : restrict (b :: B) T with
      | none => simp [OptionIso,et] at it
      | some t' =>
        have hit : RootedIso (expand a b a t) t' := by simpa [OptionIso,et] using it
        cases es : restrict (b :: B) S with
        | none => simp [OptionIso,es] at is
        | some s' =>
          have his : RootedIso (expand a b a s) s' := by simpa [OptionIso,es] using is
          have hh := rootedIso_trans (rootedIso_symm hit)
            (rootedIso_trans (expand_preserves_iso a b a iso) his)
          simpa [restrictionAgrees,et,es] using (sameShape_correct t' s').2 hh

end ForestState
