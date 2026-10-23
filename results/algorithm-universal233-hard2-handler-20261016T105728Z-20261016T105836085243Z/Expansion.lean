import StateContract

namespace ForestState
open RMAF RestrictionBridge

theorem CherryAt.restriction_cherry_exists {t : Tree} {a b : Nat} {w : Vertex}
    (h : CherryAt a b t w) (B : List Nat) (ha : a ∈ B) (hb : b ∈ B) :
    ∃ u, restrict B t = some u ∧ cherry a b u = true := by
  induction h with
  | straight => exact ⟨.node (.leaf a) (.leaf b),by simp [restrict,ha,hb],by simp [cherry]⟩
  | swapped => exact ⟨.node (.leaf b) (.leaf a),by simp [restrict,ha,hb],by simp [cherry]⟩
  | @left l r w h ih =>
    obtain ⟨u,hu,chu⟩ := ih
    cases rr : restrict B r with
    | none => exact ⟨u,by simp [restrict,hu,rr],chu⟩
    | some v => exact ⟨.node u v,by simp [restrict,hu,rr],by simp [cherry,chu]⟩
  | @right l r w h ih =>
    obtain ⟨u,hu,chu⟩ := ih
    cases rl : restrict B l with
    | none => exact ⟨u,by simp [restrict,hu,rl],chu⟩
    | some v => exact ⟨.node v u,by simp [restrict,hu,rl],by simp [cherry,chu]⟩

theorem quotient_shape_restriction (t u : Tree) (B : List Nat) (a b : Nat)
    (shape : QuotientShape a b t) (sat : a ∈ B ↔ b ∈ B) (hr : restrict B t = some u) :
    QuotientShape a b u := by
  rcases shape with ch | ⟨ha,hb⟩
  · by_cases ha : a ∈ B
    · obtain ⟨w,hw⟩ := cherry_at_exists t a b ch
      obtain ⟨v,hv,chv⟩ := hw.restriction_cherry_exists B ha (sat.mp ha)
      have he : v = u := Option.some.inj (hv.symm.trans hr)
      exact Or.inl (he ▸ chv)
    · have hb : b ∉ B := fun hm => ha (sat.mpr hm)
      exact Or.inr ⟨fun hm => ha ((restricted_labels_exact t u B hr).1 hm).2,
        fun hm => hb ((restricted_labels_exact t u B hr).1 hm).2⟩
  · exact Or.inr ⟨fun hm => ha ((restricted_labels_exact t u B hr).1 hm).1,
      fun hm => hb ((restricted_labels_exact t u B hr).1 hm).1⟩

theorem quotient_expand_contract_iso (t : Tree) (a b z : Nat) (shape : QuotientShape a b t)
    (nd : (leaves t).Nodup) (hz : z ∉ leaves t) :
    RootedIso (expand a b z (contract a b z t)) t := by
  rcases shape with ch | ⟨ha,hb⟩
  · obtain ⟨w,hw⟩ := cherry_at_exists t a b ch
    exact hw.expand_contract_iso z nd hz
  · rw [contract_absent t a b z ha,expand_absent a b z t hz]
    exact rootedIso_refl _

theorem quotient_topology_reflect (t s : Tree) (B : List Nat) (a b z : Nat)
    (ht : QuotientShape a b t) (hs : QuotientShape a b s)
    (ndt : (leaves t).Nodup) (nds : (leaves s).Nodup)
    (hzt : z ∉ leaves t) (hzs : z ∉ leaves s) (hzB : z ∉ B) (sat : a ∈ B ↔ b ∈ B)
    (h : restrictionAgrees (contract a b z t) (contract a b z s) (contractBlock a b z B) = true) :
    restrictionAgrees t s B = true := by
  have et := quotient_tree_restriction t B a b z ht ndt hzt hzB sat
  have es := quotient_tree_restriction s B a b z hs nds hzs hzB sat
  simp only [restrictionAgrees,et,es] at h
  cases rt : restrict B t with
  | none => simp [rt] at h
  | some u =>
    cases rs : restrict B s with
    | none => simp [rs] at h
    | some v =>
      have ic : RootedIso (contract a b z u) (contract a b z v) :=
        (sameShape_correct _ _).1 (by simpa [rt,rs] using h)
      have hzu : z ∉ leaves u := fun hm => hzt ((restricted_labels_exact t u B rt).1 hm).1
      have hzv : z ∉ leaves v := fun hm => hzs ((restricted_labels_exact s v B rs).1 hm).1
      have iu := quotient_expand_contract_iso u a b z (quotient_shape_restriction t u B a b ht sat rt)
        (restricted_nodup t u B rt ndt) hzu
      have iv := quotient_expand_contract_iso v a b z (quotient_shape_restriction s v B a b hs sat rs)
        (restricted_nodup s v B rs nds) hzv
      have iso := rootedIso_trans (rootedIso_symm iu) (rootedIso_trans (expand_preserves_iso a b z ic) iv)
      simpa [restrictionAgrees,rt,rs] using (sameShape_correct _ _).2 iso

theorem expandBlock_mem (C : List Nat) (a b z x : Nat) :
    x ∈ expandBlock a b z C ↔ (z ∈ C ∧ (x = a ∨ x = b)) ∨ (x ∈ C ∧ x ≠ z) := by
  simp only [expandBlock,List.mem_flatMap]
  constructor
  · rintro ⟨y,hy,hxy⟩
    by_cases he : y = z
    · subst y
      have hx : x = a ∨ x = b := by simpa using hxy
      exact Or.inl ⟨hy,hx⟩
    · have hx : x = y := by simpa [he] using hxy
      subst x
      exact Or.inr ⟨hy,he⟩
  · rintro (⟨hz,hx⟩ | ⟨hx,hxz⟩)
    · exact ⟨z,hz,by simpa using hx⟩
    · exact ⟨x,hx,by simp [hxz]⟩

theorem expandBlock_saturated (C : List Nat) (a b z : Nat) (ha : a ∉ C) (hb : b ∉ C) :
    a ∈ expandBlock a b z C ↔ b ∈ expandBlock a b z C := by
  simp [expandBlock_mem,ha,hb]

theorem expandBlock_fresh (C : List Nat) (a b z : Nat) (hza : z ≠ a) (hzb : z ≠ b) :
    z ∉ expandBlock a b z C := by simp [expandBlock_mem,hza,hzb]

theorem expandBlock_nonempty (C : List Nat) (a b z : Nat) (hne : C ≠ []) :
    expandBlock a b z C ≠ [] := by
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil C hne
  by_cases hxz : x = z
  · have hm : a ∈ expandBlock a b z C := (expandBlock_mem C a b z a).2 (Or.inl ⟨hxz ▸ hx,Or.inl rfl⟩)
    exact List.ne_nil_of_mem hm
  · exact List.ne_nil_of_mem ((expandBlock_mem C a b z x).2 (Or.inr ⟨hx,hxz⟩))

theorem contract_expandBlock_mask (C : List Nat) (a b z : Nat)
    (ha : a ∉ C) (hb : b ∉ C) (hza : z ≠ a) (hzb : z ≠ b) (x : Nat) :
    (contractBlock a b z (expandBlock a b z C)).contains x = C.contains x := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem]
  rw [contractBlock_mem _ a b z x (expandBlock_fresh C a b z hza hzb)
    (expandBlock_saturated C a b z ha hb)]
  by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [expandBlock_mem]

theorem expandBlock_count (C : List Nat) (a b z x : Nat) (hab : a ≠ b)
    (ha : a ∉ C) (hb : b ∉ C) (hza : z ≠ a) (hzb : z ≠ b) :
    (expandBlock a b z C).count x =
      if x = a ∨ x = b then C.count z else if x = z then 0 else C.count x := by
  induction C with
  | nil => simp [expandBlock]
  | cons y C ih =>
    have hya : y ≠ a := by intro he; subst y; simp at ha
    have hyb : y ≠ b := by intro he; subst y; simp at hb
    have haC : a ∉ C := fun hm => ha (by simp [hm])
    have hbC : b ∉ C := fun hm => hb (by simp [hm])
    have hi := ih haC hbC
    by_cases hyz : y = z
    · subst y
      by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxz : x = z <;>
        simp_all [expandBlock,List.count_append,List.count_cons] <;> simp_all [eq_comm] <;> omega
    · by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxz : x = z <;>
        simp_all [expandBlock,List.count_append,List.count_cons] <;> simp_all [eq_comm] <;> omega

theorem expanded_forest_count (G : List (List Nat)) (a b z x : Nat) (hab : a ≠ b)
    (ha : ∀ C ∈ G, a ∉ C) (hb : ∀ C ∈ G, b ∉ C) (hza : z ≠ a) (hzb : z ≠ b) :
    ((G.map (expandBlock a b z)).flatten).count x =
      if x = a ∨ x = b then G.flatten.count z else if x = z then 0 else G.flatten.count x := by
  induction G with
  | nil => simp
  | cons C G ih =>
    have hi := ih (fun D hD => ha D (by simp [hD])) (fun D hD => hb D (by simp [hD]))
    simp only [List.map_cons,List.flatten_cons,List.count_append,
      expandBlock_count C a b z x hab (ha C (by simp)) (hb C (by simp)) hza hzb,hi]
    by_cases hx : x = a ∨ x = b <;> by_cases hxz : x = z <;> simp [hx,hxz,hza,hzb]

end ForestState
