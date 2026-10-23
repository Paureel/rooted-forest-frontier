import CoreGraph
import Composition

/-! One-shot integration proof from the ordinary executable checker to actual
one-edge connected source supports. Frozen author modules are imported unchanged.
No generator coverage, quotient simulation, cut lift, or runtime is assumed. -/
namespace Universal233.Integration
open RMAF CoreGraph VertexGeometry

theorem valid_root (t : Tree) : Valid t [] := ⟨t, rfl⟩

theorem valid_cons (l r : Tree) (s : Bool) (v : RMAF.Vertex) :
    Valid (.node l r) (s :: v) ↔ Valid (if s then r else l) v := by
  rfl

theorem valid_leaf_only (x : Nat) (v : RMAF.Vertex) (h : Valid (.leaf x) v) : v = [] := by
  cases v with
  | nil => rfl
  | cons s v => obtain ⟨t,h⟩ := h; simp [subtree] at h

theorem adj_down (l r : Tree) (s : Bool) {u v : RMAF.Vertex}
    (h : Adj (if s then r else l) u v) : Adj (.node l r) (s :: u) (s :: v) := by
  refine ⟨h.1,h.2.1,?_⟩
  rcases h.2.2 with ⟨b,hb⟩ | ⟨b,hb⟩
  · exact Or.inl ⟨b,congrArg (s :: ·) hb⟩
  · exact Or.inr ⟨b,congrArg (s :: ·) hb⟩

theorem walk_down (l r : Tree) (s : Bool) (P : RMAF.Vertex → Prop) {u v : RMAF.Vertex}
    (h : Walk (if s then r else l) (fun w => P (s :: w)) u v) :
    Walk (.node l r) P (s :: u) (s :: v) := by
  induction h with
  | refl hp => exact .refl hp
  | step hp ha htail ih => exact .step hp (adj_down l r s ha) ih

theorem adj_root_child (l r : Tree) (s : Bool) : Adj (.node l r) [] [s] := by
  exact ⟨valid_root _,valid_root _,Or.inl ⟨s,rfl⟩⟩

theorem convex_down (P : RMAF.Vertex → Prop) (hc : Convex P) (s : Bool) :
    Convex (fun w => P (s :: w)) := by
  intro v a b ha hb hp
  exact hc _ _ _ ha hb (.down s hp)

/-- Finite original-tree walks from the root through an actual convex set. -/
theorem convex_root_walk (t : Tree) (P : RMAF.Vertex → Prop) (hc : Convex P)
    (v : RMAF.Vertex) (hv : Valid t v) (hr : P []) (hp : P v) : Walk t P [] v := by
  induction t generalizing v P with
  | leaf x =>
    have he := valid_leaf_only x v hv
    subst v
    exact .refl hr
  | node l r ihl ihr =>
    cases v with
    | nil => exact .refl hr
    | cons s v =>
      have hchild : P [s] := hc [s] [] (s :: v) hr hp (.rightLeg s (.endpointL [] v))
      apply Walk.step hr (adj_root_child l r s)
      apply walk_down l r s P
      cases s with
      | false => exact ihl _ (convex_down P hc false) v hv hchild hp
      | true => exact ihr _ (convex_down P hc true) v hv hchild hp

/-- Address-convex actual source supports are connected by proved one-edge walks. -/
theorem convex_connected (t : Tree) (P : RMAF.Vertex → Prop) (hc : Convex P)
    (u v : RMAF.Vertex) (hu : Valid t u) (hv : Valid t v) (hPu : P u) (hPv : P v) :
    Walk t P u v := by
  induction t generalizing P u v with
  | leaf x =>
    have he := valid_leaf_only x u hu
    have hf := valid_leaf_only x v hv
    subst u; subst v
    exact .refl hPu
  | node l r ihl ihr =>
    cases u with
    | nil => exact convex_root_walk _ _ hc v hv hPu hPv
    | cons s u =>
      cases v with
      | nil => exact (convex_root_walk _ _ hc (s :: u) hu hPv hPu).reverse
      | cons z v =>
        cases s <;> cases z
        · exact walk_down l r false P (ihl _ (convex_down P hc false) u v hu hv hPu hPv)
        · have hr : P [] := hc [] (false :: u) (true :: v) hPu hPv (.fork u v)
          exact (convex_root_walk _ _ hc _ hu hr hPu).reverse.trans
            (convex_root_walk _ _ hc _ hv hr hPv)
        · have hr : P [] := hc [] (true :: u) (false :: v) hPu hPv (.fork' u v)
          exact (convex_root_walk _ _ hc _ hu hr hPu).reverse.trans
            (convex_root_walk _ _ hc _ hv hr hPv)
        · exact walk_down l r true P (ihr _ (convex_down P hc true) u v hu hv hPu hPv)

theorem rootedSpan_actual (D : List Nat) (t : Tree) (v : RMAF.Vertex)
    (h : v ∈ RMAF.rootedSpan D t) : Valid t v := by
  induction t generalizing v with
  | leaf x =>
    simp only [RMAF.rootedSpan] at h
    split at h
    · have he : v = [] := by simpa using h
      subst v; exact valid_root _
    · simp at h
  | node l r ihl ihr =>
    cases v with
    | nil => exact valid_root _
    | cons s v =>
      cases s <;> simp only [RMAF.rootedSpan] at h <;> split at h
      all_goals simp_all [RMAF.prependSide, valid_cons]

theorem minimalVertices_actual (D : List Nat) (t : Tree) (v : RMAF.Vertex)
    (h : v ∈ RMAF.minimalVertices D t) : Valid t v := by
  induction t generalizing v with
  | leaf x =>
    simp only [RMAF.minimalVertices] at h
    split at h
    · have he : v = [] := by simpa using h
      subst v; exact valid_root _
    · simp at h
  | node l r ihl ihr =>
    cases v with
    | nil => exact valid_root _
    | cons s v =>
      cases s <;> simp only [RMAF.minimalVertices] at h <;> split at h
      all_goals try split at h
      all_goals simp_all [RMAF.prependSide, valid_cons]
      all_goals first | exact rootedSpan_actual D l v h | exact rootedSpan_actual D r v h

/-- The exact executable minimal-embedding supports have actual graph walks. -/
theorem minimalVertices_connected (D : List Nat) (t : Tree) (u v : RMAF.Vertex)
    (hu : u ∈ RMAF.minimalVertices D t) (hv : v ∈ RMAF.minimalVertices D t) :
    Walk t (fun w => w ∈ RMAF.minimalVertices D t) u v := by
  have hc : Convex (fun w => w ∈ RMAF.minimalVertices D t) := by
    simpa only [minimalVertices_correct] using hull_convex (selectedLeaves D t)
  exact convex_connected t _ hc u v (minimalVertices_actual D t u hu)
    (minimalVertices_actual D t v hv) hu hv

theorem leafAt_selected (t : Tree) (v : RMAF.Vertex) (x : Nat) :
    LeafAt t v x ↔ selectedLeaves [x] t v := by
  induction t generalizing v with
  | leaf y =>
    cases v with
    | nil => simp [LeafAt,subtree,selectedLeaves,eq_comm]
    | cons s v => simp [LeafAt,subtree,selectedLeaves]
  | node l r ihl ihr =>
    cases v with
    | nil => simp [LeafAt,subtree,selectedLeaves,Join]
    | cons s v => cases s <;> simpa [LeafAt,subtree,selectedLeaves,Join] using (by
      first | exact ihl v | exact ihr v)

theorem selected_at_leaf (D : List Nat) (t : Tree) (v : RMAF.Vertex) (x : Nat)
    (h : LeafAt t v x) : selectedLeaves D t v ↔ x ∈ D := by
  induction t generalizing v with
  | leaf y =>
    cases v with
    | nil => have he : y = x := by simpa [LeafAt,subtree] using h
             subst y; simp [selectedLeaves]
    | cons s v => simp [LeafAt,subtree] at h
  | node l r ihl ihr =>
    cases v with
    | nil => simp [LeafAt,subtree] at h
    | cons s v => cases s <;> first | exact ihl v h | exact ihr v h

theorem minimalVertices_terminal (D : List Nat) (t : Tree) (v : RMAF.Vertex) (x : Nat)
    (h : LeafAt t v x) : v ∈ RMAF.minimalVertices D t ↔ x ∈ D := by
  rw [minimalVertices_correct]
  constructor
  · intro hh
    have hs := selected_leaf_reach_implies_self [x] D t v
      ((leafAt_selected t v x).1 h) (hull_subset_reach _ v hh)
    exact (selected_at_leaf D t v x h).1 hs
  · intro hx
    have hs := (selected_at_leaf D t v x h).2 hx
    exact ⟨v,v,hs,hs,.endpointL v v⟩

theorem partitionCheck_covers (labels : List Nat) (bs : List (List Nat))
    (h : RMAF.partitionCheck labels bs = true) (x : Nat) (hx : x ∈ labels) :
    ∃ b, b ∈ bs ∧ x ∈ b := by
  have hc : labels.all (fun y => bs.flatten.count y == 1) = true := by
    simp only [RMAF.partitionCheck,Bool.and_eq_true] at h
    simp_all
  have hxcount : bs.flatten.count x = 1 := by
    exact beq_iff_eq.1 ((List.all_eq_true.1 hc) x hx)
  exact List.mem_flatten.1 (List.count_pos_iff.1 (by omega))

theorem leafAt_label (t : Tree) (v : RMAF.Vertex) (x : Nat) (h : LeafAt t v x) :
    x ∈ RMAF.leaves t :=
  (singleton_selected_exists t x).1 ⟨v,(leafAt_selected t v x).1 h⟩

theorem checked_support_unique (t : Tree) (bs : List (List Nat))
    (he : RMAF.pairwiseEmbeddings t bs = true) (b c : List Nat)
    (hb : b ∈ bs) (hc : c ∈ bs) (v : RMAF.Vertex)
    (hv : v ∈ RMAF.minimalVertices b t) (hw : v ∈ RMAF.minimalVertices c t) : b = c := by
  classical
  apply Classical.byContradiction
  intro hne
  have hd := pairwise_rel_of_distinct_mem
    (fun D E => ∀ w, ¬(Hull (selectedLeaves D t) w ∧ Hull (selectedLeaves E t) w))
    (fun D E h w hh => h w ⟨hh.2,hh.1⟩) bs
    ((executable_pairwiseEmbeddings t bs).1 he) b c hb hc hne
  exact hd v ⟨(minimalVertices_correct b t v).1 hv,(minimalVertices_correct c t v).1 hw⟩

theorem idxOf_injective_on (bs : List (List Nat)) (b c : List Nat)
    (hb : b ∈ bs) (hc : c ∈ bs) (hi : bs.idxOf b = bs.idxOf c) : b = c := by
  have hbi := List.idxOf_lt_length_of_mem hb
  have hci := List.idxOf_lt_length_of_mem hc
  have hbe := List.getElem_idxOf hbi
  have hce := List.getElem_idxOf hci
  simp only [hi] at hbe
  exact hbe.symm.trans hce

def HasCheckedSupport (t : Tree) (bs : List (List Nat)) (v : RMAF.Vertex) : Prop :=
  ∃ b, b ∈ bs ∧ v ∈ RMAF.minimalVertices b t

noncomputable def checkedOwner (t : Tree) (bs : List (List Nat)) (v : RMAF.Vertex) : Nat := by
  classical
  exact if h : HasCheckedSupport t bs v then bs.idxOf h.choose else bs.length

def checkedSupport (t : Tree) (bs : List (List Nat)) (i : Nat) (v : RMAF.Vertex) : Prop :=
  ∃ b, b ∈ bs ∧ bs.idxOf b = i ∧ v ∈ RMAF.minimalVertices b t

theorem checkedOwner_at_support (t : Tree) (bs : List (List Nat))
    (he : RMAF.pairwiseEmbeddings t bs = true) (b : List Nat) (hb : b ∈ bs)
    (v : RMAF.Vertex) (hv : v ∈ RMAF.minimalVertices b t) :
    checkedOwner t bs v = bs.idxOf b := by
  classical
  have hh : HasCheckedSupport t bs v := ⟨b,hb,hv⟩
  rw [checkedOwner, dite_eq_left hh]
  have heq := checked_support_unique t bs he hh.choose b
    hh.choose_spec.1 hb v hh.choose_spec.2 hv
  exact congrArg (bs.idxOf ·) heq

theorem checkedSupport_terminal (t : Tree) (bs : List (List Nat))
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true)
    (i : Nat) (v : RMAF.Vertex) (x : Nat) (hv : LeafAt t v x) :
    checkedSupport t bs i v ↔ checkedOwner t bs v = i := by
  obtain ⟨b,hb,hx⟩ := partitionCheck_covers _ bs hp x (leafAt_label t v x hv)
  have hvs := (minimalVertices_terminal b t v x hv).2 hx
  have ho := checkedOwner_at_support t bs he b hb v hvs
  constructor
  · rintro ⟨c,hc,hci,hvc⟩
    exact (checkedOwner_at_support t bs he c hc v hvc).trans hci
  · intro h
    exact ⟨b,hb,ho.symm.trans h,hvs⟩

/-- Source partition constructed from the exact Boolean call-site conditions.
Its support connectedness is discharged by actual original-tree walks. -/
noncomputable def checkedSourcePartition (t : Tree) (bs : List (List Nat))
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true) : SourcePartition t where
  owner := checkedOwner t bs
  support := checkedSupport t bs
  actual := by
    intro i v hv
    obtain ⟨b,hb,hbi,hv⟩ := hv
    exact minimalVertices_actual b t v hv
  terminal_exact := checkedSupport_terminal t bs hp he
  connected := by
    intro i u v hu hv
    obtain ⟨b,hb,hbi,hu⟩ := hu
    obtain ⟨c,hc,hci,hv⟩ := hv
    have heq := idxOf_injective_on bs b c hb hc (hbi.trans hci.symm)
    subst c
    exact (minimalVertices_connected b t u v hu hv).mono
      (fun w hw => ⟨b,hb,hbi,hw⟩)
  disjoint := by
    intro i j v hi hj
    obtain ⟨b,hb,hbi,hv⟩ := hi
    obtain ⟨c,hc,hci,hw⟩ := hj
    have heq := checked_support_unique t bs he b c hb hc v hv hw
    subst c
    exact hbi.symm.trans hci

/-- Exact original-label owner equivalence at the ordinary solver's checker
interface; no source partition, connectedness, or hull validity is assumed. -/
theorem checkedSourcePartition_owner (t : Tree) (bs : List (List Nat))
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true)
    (u v : RMAF.Vertex) (x y : Nat) (hu : LeafAt t u x) (hv : LeafAt t v y) :
    (checkedSourcePartition t bs hp he).owner u = (checkedSourcePartition t bs hp he).owner v ↔
      ∃ b, b ∈ bs ∧ x ∈ b ∧ y ∈ b := by
  obtain ⟨b,hb,hx⟩ := partitionCheck_covers _ bs hp x (leafAt_label t u x hu)
  obtain ⟨c,hc,hy⟩ := partitionCheck_covers _ bs hp y (leafAt_label t v y hv)
  have hus := (minimalVertices_terminal b t u x hu).2 hx
  have hvs := (minimalVertices_terminal c t v y hv).2 hy
  change checkedOwner t bs u = checkedOwner t bs v ↔ _
  rw [checkedOwner_at_support t bs he b hb u hus,checkedOwner_at_support t bs he c hc v hvs]
  constructor
  · intro hi
    have heq := idxOf_injective_on bs b c hb hc hi
    subst c
    exact ⟨b,hb,hx,hy⟩
  · rintro ⟨d,hd,hxd,hyd⟩
    have hbd := checked_support_unique t bs he b d hb hd u hus
      ((minimalVertices_terminal d t u x hu).2 hxd)
    have hcd := checked_support_unique t bs he c d hc hd v hvs
      ((minimalVertices_terminal d t v y hv).2 hyd)
    rw [hbd,hcd]

theorem checkedSourcePartition_monochromatic (t : Tree) (bs : List (List Nat))
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true) (color : Nat → Nat)
    (hm : ∀ b, b ∈ bs → LabelMonochromatic color b) :
    Monochromatic (checkedSourcePartition t bs hp he) color := by
  intro u v x y hu hv ho
  obtain ⟨b,hb,hx,hy⟩ := (checkedSourcePartition_owner t bs hp he u v x y hu hv).1 ho
  exact hm b hb x y hx hy

/-- The formerly missing external consumer, now constructed with all actual
support obligations and the exact original-label equivalence discharged. -/
theorem sourcePartition_from_checks (t : Tree) (bs : List (List Nat))
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true) :
    ∃ P : SourcePartition t, ∀ u v x y, LeafAt t u x → LeafAt t v y →
      (P.owner u = P.owner v ↔ ∃ b, b ∈ bs ∧ x ∈ b ∧ y ∈ b) :=
  ⟨checkedSourcePartition t bs hp he,checkedSourcePartition_owner t bs hp he⟩

end Universal233.Integration
