import Contract
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem isMarker_false_of_absent (m : Nat) (t : Tree) (h : m∉leaves t) : isMarker m t=false := by
  cases he : isMarker m t with
  | false => rfl
  | true =>
    have ht := isMarker_true m t he
    subst t
    exact False.elim (h (by simp [leaves]))

theorem markerJoin_right_absent (m : Nat) (a b : Tree) (h : m∉leaves b) :
    markerJoin m a b=.node a b := by
  simp [markerJoin,h,isMarker_false_of_absent m b h]

theorem markerJoin_left_absent (m : Nat) (a b : Tree) (h : m∉leaves a) :
    markerJoin m a b=.node a b := by
  simp [markerJoin,h,isMarker_false_of_absent m a h]

theorem markerJoin_absorb_right (m : Nat) (a : Tree) (h : m∈leaves a) :
    markerJoin m a (.leaf m)=a := by
  by_cases hm : isMarker m a=true
  · have he := isMarker_true m a hm
    subst a
    exact markerJoin_marker m
  · have hmf : isMarker m a=false := by cases he : isMarker m a <;> simp_all
    unfold markerJoin
    rw [hmf]
    simp [isMarker,leaves,h]

theorem markerJoin_absorb_left (m : Nat) (a : Tree) (h : m∈leaves a) :
    markerJoin m (.leaf m) a=a := by
  simp [markerJoin,isMarker,leaves,h]

/-- Descendant-side contraction: all original complementary branches keep
their literal labels, while the selected subtree is replaced by one marker. -/
theorem Port.contract_hole (c : Port) (u : Tree) (Y : List Nat) (m : Nat)
    (hu : leaves u⊆Y) (hc : ∀x∈c.labels,x∉Y) (fresh : m∉c.labels) :
    contract Y m (c.plug u)=c.plug (.leaf m) := by
  induction c with
  | hole => exact contract_all Y m u hu
  | left c r ih =>
    have hC : ∀x∈c.labels,x∉Y := fun x hx => hc x (List.mem_append_left _ hx)
    have hR : ∀x∈leaves r,x∉Y := fun x hx => hc x (List.mem_append_right _ hx)
    have fC : m∉c.labels := fun hx => fresh (List.mem_append_left _ hx)
    have fR : m∉leaves r := fun hx => fresh (List.mem_append_right _ hx)
    simp only [Port.plug,contract,ih hC fC,contract_none Y m r hR fR,
      markerJoin_right_absent m _ r fR]
  | right l c ih =>
    have hC : ∀x∈c.labels,x∉Y := fun x hx => hc x (List.mem_append_right _ hx)
    have hL : ∀x∈leaves l,x∉Y := fun x hx => hc x (List.mem_append_left _ hx)
    have fC : m∉c.labels := fun hx => fresh (List.mem_append_right _ hx)
    have fL : m∉leaves l := fun hx => fresh (List.mem_append_left _ hx)
    simp only [Port.plug,contract,ih hC fC,contract_none Y m l hL fL,
      markerJoin_left_absent m l _ fL]

/-- Root-side contraction: however many original ancestors survive, their
complementary branches normalize to a single root marker attachment. -/
theorem Port.contract_complement (c : Port) (u : Tree) (Y : List Nat) (m : Nat)
    (hu : ∀x∈leaves u,x∉Y) (hc : c.labels⊆Y) (fresh : m∉leaves u) (ne : c≠.hole) :
    RootedIso (contract Y m (c.plug u)) (.node u (.leaf m)) := by
  induction c with
  | hole => exact False.elim (ne rfl)
  | left c r ih =>
    have hC : c.labels⊆Y := fun _ hx => hc (List.mem_append_left _ hx)
    have hR : leaves r⊆Y := fun _ hx => hc (List.mem_append_right _ hx)
    simp only [Port.plug,contract,contract_all Y m r hR]
    by_cases e : c=.hole
    · subst c
      simp only [Port.plug,contract_none Y m u hu fresh,markerJoin_left_absent m u _ fresh]
      exact rootedIso_refl _
    · have hi := ih hC e
      have hm : m∈leaves (contract Y m (c.plug u)) :=
        (BinaryExchange.iso_leaves hi m).2 (by simp [leaves])
      rw [markerJoin_absorb_right m _ hm]
      exact hi
  | right l c ih =>
    have hC : c.labels⊆Y := fun _ hx => hc (List.mem_append_right _ hx)
    have hL : leaves l⊆Y := fun _ hx => hc (List.mem_append_left _ hx)
    simp only [Port.plug,contract,contract_all Y m l hL]
    by_cases e : c=.hole
    · subst c
      simp only [Port.plug,contract_none Y m u hu fresh,markerJoin_right_absent m _ u fresh]
      exact .swapped (.leaf m) (rootedIso_refl u)
    · have hi := ih hC e
      have hm : m∈leaves (contract Y m (c.plug u)) :=
        (BinaryExchange.iso_leaves hi m).2 (by simp [leaves])
      rw [markerJoin_absorb_left m _ hm]
      exact hi
end OrdinaryCommonSplit
