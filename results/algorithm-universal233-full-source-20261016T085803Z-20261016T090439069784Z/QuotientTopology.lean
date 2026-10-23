import QuotientGeometry

namespace ForestState
open RMAF RestrictionBridge

theorem rootedIso_leaf_iff {t u : Tree} (h : RootedIso t u) (x : Nat) :
    t = .leaf x ↔ u = .leaf x := by
  cases h <;> simp

theorem contract_preserves_iso (a b z : Nat) {t u : Tree} (h : RootedIso t u) :
    RootedIso (contract a b z t) (contract a b z u) := by
  induction h with
  | leaf x => exact RootedIso.leaf x
  | @straight l r u v h1 h2 ih1 ih2 =>
    have he : (l == .leaf a && r == .leaf b || l == .leaf b && r == .leaf a) =
        (u == .leaf a && v == .leaf b || u == .leaf b && v == .leaf a) := by
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,rootedIso_leaf_iff h1,rootedIso_leaf_iff h2]
    cases hh : (u == .leaf a && v == .leaf b || u == .leaf b && v == .leaf a)
    · simp only [contract,he,hh,Bool.false_eq_true,ite_false]
      exact RootedIso.straight ih1 ih2
    · simp only [contract,he,hh,ite_true]
      exact RootedIso.leaf z
  | @swapped l r u v h1 h2 ih1 ih2 =>
    have he : (l == .leaf a && r == .leaf b || l == .leaf b && r == .leaf a) =
        (u == .leaf a && v == .leaf b || u == .leaf b && v == .leaf a) := by
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,rootedIso_leaf_iff h1,rootedIso_leaf_iff h2]
      constructor <;> rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
      · exact Or.inr ⟨h2,h1⟩
      · exact Or.inl ⟨h2,h1⟩
      · exact Or.inr ⟨h2,h1⟩
      · exact Or.inl ⟨h2,h1⟩
    cases hh : (u == .leaf a && v == .leaf b || u == .leaf b && v == .leaf a)
    · simp only [contract,he,hh,Bool.false_eq_true,ite_false]
      exact RootedIso.swapped ih1 ih2
    · simp only [contract,he,hh,ite_true]
      exact RootedIso.leaf z

theorem option_restricted_absent (t : Tree) (B : List Nat) (x : Nat) (hx : x ∉ leaves t) :
    x ∉ optionLeaves (restrict B t) := by
  cases hr : restrict B t with
  | none => simp [optionLeaves]
  | some u =>
    intro hm
    exact hx ((restricted_labels_exact t u B hr).1 hm).1

theorem contract_join_right_absent (a b z : Nat) (l r : Option Tree)
    (ha : a ∉ optionLeaves r) (hb : b ∉ optionLeaves r) :
    (join l r).map (contract a b z) =
      join (l.map (contract a b z)) (r.map (contract a b z)) := by
  cases l with
  | none => cases r <;> rfl
  | some u =>
    cases r with
    | none => rfl
    | some v =>
      have eva : v ≠ .leaf a := by intro he; subst v; simp [optionLeaves,leaves] at ha
      have evb : v ≠ .leaf b := by intro he; subst v; simp [optionLeaves,leaves] at hb
      simp [join,contract,eva,evb]

theorem contract_join_left_absent (a b z : Nat) (l r : Option Tree)
    (ha : a ∉ optionLeaves l) (hb : b ∉ optionLeaves l) :
    (join l r).map (contract a b z) =
      join (l.map (contract a b z)) (r.map (contract a b z)) := by
  cases r with
  | none => cases l <;> rfl
  | some v =>
    cases l with
    | none => rfl
    | some u =>
      have eua : u ≠ .leaf a := by intro he; subst u; simp [optionLeaves,leaves] at ha
      have eub : u ≠ .leaf b := by intro he; subst u; simp [optionLeaves,leaves] at hb
      simp [join,contract,eua,eub]

theorem CherryAt.contract_restriction {t : Tree} {a b : Nat} {w : Vertex}
    (h : CherryAt a b t w) (z : Nat) (B : List Nat) (nd : (leaves t).Nodup)
    (hz : z ∉ leaves t) (hzB : z ∉ B) (sat : a ∈ B ↔ b ∈ B) :
    restrict (contractBlock a b z B) (contract a b z t) =
      (restrict B t).map (contract a b z) := by
  induction h with
  | straight =>
    by_cases haB : a ∈ B
    · have hbB := sat.mp haB
      have hzC := (contractBlock_z B a b z hzB).2 haB
      simp [contract,restrict,haB,hbB,hzC]
    · have hbB : b ∉ B := fun hm => haB (sat.mpr hm)
      have hzC : z ∉ contractBlock a b z B := fun hm => haB ((contractBlock_z B a b z hzB).1 hm)
      simp [contract,restrict,haB,hbB,hzC]
  | swapped =>
    by_cases haB : a ∈ B
    · have hbB := sat.mp haB
      have hzC := (contractBlock_z B a b z hzB).2 haB
      simp [contract,restrict,haB,hbB,hzC]
    · have hbB : b ∉ B := fun hm => haB (sat.mpr hm)
      have hzC : z ∉ contractBlock a b z B := fun hm => haB ((contractBlock_z B a b z hzB).1 hm)
      simp [contract,restrict,haB,hbB,hzC]
  | @left l r w h ih =>
    have ndl : (leaves l).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nar := nodup_append_avoid_right l r a nd h.labels.1
    have nbr := nodup_append_avoid_right l r b nd h.labels.2
    have hzl : z ∉ leaves l := fun hx => hz (by simp [leaves,hx])
    have hzr : z ∉ leaves r := fun hx => hz (by simp [leaves,hx])
    have el : ∀ c, l ≠ .leaf c := by intro c he; subst l; cases h
    have cc : contract a b z (.node l r) = .node (contract a b z l) r := by
      simp [contract,el,contract_absent r a b z nar]
    rw [cc,restrict_node,ih ndl hzl,
      ←restrict_mask_equal r B (contractBlock a b z B) (contracted_mask_absent r B a b z nar nbr hzr),
      restrict_node,contract_join_right_absent a b z _ _
        (option_restricted_absent r B a nar) (option_restricted_absent r B b nbr)]
    congr 1
    cases rr : restrict B r with
    | none => rfl
    | some v =>
      have av : a ∉ leaves v := by
        intro hm; exact nar ((restricted_labels_exact r v B rr).1 hm).1
      simp [contract_absent v a b z av]
  | @right l r w h ih =>
    have ndr : (leaves r).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nal := nodup_append_avoid_left l r a nd h.labels.1
    have nbl := nodup_append_avoid_left l r b nd h.labels.2
    have hzl : z ∉ leaves l := fun hx => hz (by simp [leaves,hx])
    have hzr : z ∉ leaves r := fun hx => hz (by simp [leaves,hx])
    have er : ∀ c, r ≠ .leaf c := by intro c he; subst r; cases h
    have cc : contract a b z (.node l r) = .node l (contract a b z r) := by
      simp [contract,er,contract_absent l a b z nal]
    rw [cc,restrict_node,ih ndr hzr,
      ←restrict_mask_equal l B (contractBlock a b z B) (contracted_mask_absent l B a b z nal nbl hzl),
      restrict_node,contract_join_left_absent a b z _ _
        (option_restricted_absent l B a nal) (option_restricted_absent l B b nbl)]
    congr 1
    cases rl : restrict B l with
    | none => rfl
    | some u =>
      have au : a ∉ leaves u := by
        intro hm; exact nal ((restricted_labels_exact l u B rl).1 hm).1
      simp [contract_absent u a b z au]

end ForestState
