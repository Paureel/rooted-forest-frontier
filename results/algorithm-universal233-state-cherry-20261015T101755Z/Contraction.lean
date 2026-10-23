import Replacement

namespace ForestState
open RMAF RestrictionBridge

theorem contract_absent (t : Tree) (a b z : Nat) (ha : a ∉ leaves t) :
    contract a b z t = t := by
  induction t with
  | leaf x => rfl
  | node l r hl hr =>
    have hal : a ∉ leaves l := fun hx => ha (by simp [leaves,hx])
    have har : a ∉ leaves r := fun hx => ha (by simp [leaves,hx])
    have el : l ≠ .leaf a := by intro he; subst l; simp [leaves] at hal
    have er : r ≠ .leaf a := by intro he; subst r; simp [leaves] at har
    simp [contract,el,er,hl hal,hr har]

theorem CherryAt.contract_count {t : Tree} {a b : Nat} {w : Vertex}
    (h : CherryAt a b t w) (z x : Nat) (nd : (leaves t).Nodup) (hz : z ∉ leaves t) :
    (leaves (contract a b z t)).count x =
      if x = z then 1 else if x = a ∨ x = b then 0 else (leaves t).count x := by
  induction h with
  | straight =>
    have hza : z ≠ a := by intro he; subst z; simp [leaves] at hz
    have hzb : z ≠ b := by intro he; subst z; simp [leaves] at hz
    by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp_all [contract,leaves,List.count_cons] <;> simp_all [eq_comm]
  | swapped =>
    have hza : z ≠ a := by intro he; subst z; simp [leaves] at hz
    have hzb : z ≠ b := by intro he; subst z; simp [leaves] at hz
    by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp_all [contract,leaves,List.count_cons] <;> simp_all [eq_comm]
  | @left l r w h ih =>
    have ndl : (leaves l).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nar := nodup_append_avoid_right l r a nd h.labels.1
    have nbr := nodup_append_avoid_right l r b nd h.labels.2
    have hzl : z ∉ leaves l := fun hx => hz (by simp [leaves,hx])
    have hzr : z ∉ leaves r := fun hx => hz (by simp [leaves,hx])
    have ela : l ≠ .leaf a := by
      intro he; subst l
      have hb := h.labels.2
      have hba : b = a := by simpa [leaves] using hb
      subst b
      cases h
    have elb : l ≠ .leaf b := by intro he; subst l; cases h
    have el : ∀ c, l ≠ .leaf c := by intro c he; subst l; cases h
    simp only [contract,show (l == .leaf a && r == .leaf b || l == .leaf b && r == .leaf a) = false by simp [el],
      Bool.false_eq_true,if_false,leaves,List.count_append,contract_absent r a b z nar]
    rw [ih ndl hzl]
    by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp_all [List.count_eq_zero.2 nar,List.count_eq_zero.2 nbr,List.count_eq_zero.2 hzr]
  | @right l r w h ih =>
    have ndr : (leaves r).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nal := nodup_append_avoid_left l r a nd h.labels.1
    have nbl := nodup_append_avoid_left l r b nd h.labels.2
    have hzl : z ∉ leaves l := fun hx => hz (by simp [leaves,hx])
    have hzr : z ∉ leaves r := fun hx => hz (by simp [leaves,hx])
    have er : ∀ c, r ≠ .leaf c := by intro c he; subst r; cases h
    simp only [contract,show (l == .leaf a && r == .leaf b || l == .leaf b && r == .leaf a) = false by simp [er],
      Bool.false_eq_true,if_false,leaves,List.count_append,contract_absent l a b z nal]
    rw [ih ndr hzr]
    by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp_all [List.count_eq_zero.2 nal,List.count_eq_zero.2 nbl,List.count_eq_zero.2 hzl]

theorem contraction_nodup (t : Tree) (a b z : Nat) (nd : (leaves t).Nodup)
    (ch : cherry a b t = true) (hz : z ∉ leaves t) : (leaves (contract a b z t)).Nodup := by
  obtain ⟨w,hw⟩ := cherry_at_exists t a b ch
  apply List.nodup_iff_count.2
  intro x
  rw [hw.contract_count z x nd hz]
  split
  · omega
  · split
    · omega
    · exact List.nodup_iff_count.1 nd x

theorem CherryAt.contract_length {t : Tree} {a b : Nat} {w : Vertex}
    (h : CherryAt a b t w) (z : Nat) (nd : (leaves t).Nodup) :
    (leaves (contract a b z t)).length + 1 = (leaves t).length := by
  induction h with
  | straight => simp [contract,leaves]
  | swapped => simp [contract,leaves]
  | @left l r w h ih =>
    have ndl : (leaves l).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nar := nodup_append_avoid_right l r a nd h.labels.1
    have el : ∀ c, l ≠ .leaf c := by intro c he; subst l; cases h
    simp only [contract,show (l == .leaf a && r == .leaf b || l == .leaf b && r == .leaf a) = false by simp [el],
      Bool.false_eq_true,if_false,leaves,List.length_append,contract_absent r a b z nar]
    have hi := ih ndl
    omega
  | @right l r w h ih =>
    have ndr : (leaves r).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nal := nodup_append_avoid_left l r a nd h.labels.1
    have er : ∀ c, r ≠ .leaf c := by intro c he; subst r; cases h
    simp only [contract,show (l == .leaf a && r == .leaf b || l == .leaf b && r == .leaf a) = false by simp [er],
      Bool.false_eq_true,if_false,leaves,List.length_append,contract_absent l a b z nal]
    have hi := ih ndr
    omega

theorem CherryAt.expand_contract_iso {t : Tree} {a b : Nat} {w : Vertex}
    (h : CherryAt a b t w) (z : Nat) (nd : (leaves t).Nodup) (hz : z ∉ leaves t) :
    RootedIso (expand a b z (contract a b z t)) t := by
  induction h with
  | straight => simp [contract,expand]; exact rootedIso_refl _
  | swapped =>
    simp only [contract,BEq.rfl,Bool.and_self,Bool.or_true,if_true,expand]
    exact RootedIso.swapped (RootedIso.leaf a) (RootedIso.leaf b)
  | @left l r w h ih =>
    have ndl : (leaves l).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nar := nodup_append_avoid_right l r a nd h.labels.1
    have hzl : z ∉ leaves l := fun hx => hz (by simp [leaves,hx])
    have hzr : z ∉ leaves r := fun hx => hz (by simp [leaves,hx])
    have el : ∀ c, l ≠ .leaf c := by intro c he; subst l; cases h
    simp only [contract,show (l == .leaf a && r == .leaf b || l == .leaf b && r == .leaf a) = false by simp [el],
      Bool.false_eq_true,if_false,expand,contract_absent r a b z nar,expand_absent a b z r hzr]
    exact RootedIso.straight (ih ndl hzl) (rootedIso_refl r)
  | @right l r w h ih =>
    have ndr : (leaves r).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nal := nodup_append_avoid_left l r a nd h.labels.1
    have hzl : z ∉ leaves l := fun hx => hz (by simp [leaves,hx])
    have hzr : z ∉ leaves r := fun hx => hz (by simp [leaves,hx])
    have er : ∀ c, r ≠ .leaf c := by intro c he; subst r; cases h
    simp only [contract,show (l == .leaf a && r == .leaf b || l == .leaf b && r == .leaf a) = false by simp [er],
      Bool.false_eq_true,if_false,expand,contract_absent l a b z nal,expand_absent a b z l hzl]
    exact RootedIso.straight (rootedIso_refl l) (ih ndr hzr)

theorem expanded_not_endpoint (t : Tree) (a b z : Nat) (ha : a ∉ leaves t) (hb : b ∉ leaves t) :
    expand a b z t ≠ .leaf a ∧ expand a b z t ≠ .leaf b := by
  cases t with
  | leaf x =>
    have hxa : x ≠ a := by simpa [leaves,eq_comm] using ha
    have hxb : x ≠ b := by simpa [leaves,eq_comm] using hb
    by_cases hxz : x = z <;> simp [expand,hxz,hxa,hxb]
  | node l r => simp [expand]

theorem contract_expand_inverse (t : Tree) (a b z : Nat) (ha : a ∉ leaves t) (hb : b ∉ leaves t) :
    contract a b z (expand a b z t) = t := by
  induction t with
  | leaf x => by_cases hxz : x = z <;> simp [expand,contract,hxz]
  | node l r hl hr =>
    have hal : a ∉ leaves l := fun hx => ha (by simp [leaves,hx])
    have har : a ∉ leaves r := fun hx => ha (by simp [leaves,hx])
    have hbl : b ∉ leaves l := fun hx => hb (by simp [leaves,hx])
    have hbr : b ∉ leaves r := fun hx => hb (by simp [leaves,hx])
    have el := expanded_not_endpoint l a b z hal hbl
    have er := expanded_not_endpoint r a b z har hbr
    simp [expand,contract,el,er,hl hal hbl,hr har hbr]

theorem cherry_ready_strict_decrease (t : Tree) (ss : List Tree) (a b z : Nat)
    (h : cherryReady (some t) ss a b z = true) :
    (leaves (contract a b z t)).length + 1 = (labels (some t)).length := by
  have hh : proper (some t) ss = true ∧ a ≠ b ∧ z ∉ labels (some t) ∧
      cherry a b t = true ∧ ∃ s ∈ ss, cherry a b s = true := by
    simpa [cherryReady,Bool.and_eq_true,List.any_eq_true,and_assoc] using h
  obtain ⟨w,hw⟩ := cherry_at_exists t a b hh.2.2.2.1
  exact hw.contract_length z (proper_parts (some t) ss hh.1).1

end ForestState
