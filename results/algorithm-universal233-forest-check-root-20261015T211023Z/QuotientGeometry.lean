import BlockPartition

namespace ForestState
open RMAF RestrictionBridge

theorem contractBlock_z (B : List Nat) (a b z : Nat) (hz : z ∉ B) :
    z ∈ contractBlock a b z B ↔ a ∈ B := by
  by_cases ha : a ∈ B <;> simp [contractBlock,ha,hz]

theorem contractBlock_other_mask (B : List Nat) (a b z x : Nat)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxz : x ≠ z) :
    B.contains x = (contractBlock a b z B).contains x := by
  apply Bool.eq_iff_iff.2
  by_cases ha : a ∈ B <;> simp [contractBlock,ha,hxa,hxb,hxz]

theorem contracted_mask_absent (t : Tree) (B : List Nat) (a b z : Nat)
    (ha : a ∉ leaves t) (hb : b ∉ leaves t) (hz : z ∉ leaves t) :
    ∀ x ∈ leaves t, B.contains x = (contractBlock a b z B).contains x := by
  intro x hx
  apply contractBlock_other_mask
  · intro he; subst x; exact ha hx
  · intro he; subst x; exact hb hx
  · intro he; subst x; exact hz hx

theorem node_quotient_clear_congr (l r u v : Tree) (B C D E : List Nat)
    (ebl : (rootedSpan B l).isEmpty = (rootedSpan D u).isEmpty)
    (ebr : (rootedSpan B r).isEmpty = (rootedSpan D v).isEmpty)
    (ecl : (rootedSpan C l).isEmpty = (rootedSpan E u).isEmpty)
    (ecr : (rootedSpan C r).isEmpty = (rootedSpan E v).isEmpty)
    (hlroot : Clear (rootedSpan B l) (minimalVertices C l) ↔ Clear (rootedSpan D u) (minimalVertices E u))
    (hrroot : Clear (rootedSpan B r) (minimalVertices C r) ↔ Clear (rootedSpan D v) (minimalVertices E v))
    (hlback : Clear (rootedSpan C l) (minimalVertices B l) ↔ Clear (rootedSpan E u) (minimalVertices D u))
    (hrback : Clear (rootedSpan C r) (minimalVertices B r) ↔ Clear (rootedSpan E v) (minimalVertices D v))
    (hlmin : Clear (minimalVertices B l) (minimalVertices C l) ↔ Clear (minimalVertices D u) (minimalVertices E u))
    (hrmin : Clear (minimalVertices B r) (minimalVertices C r) ↔ Clear (minimalVertices D v) (minimalVertices E v)) :
    (Clear (rootedSpan B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (rootedSpan D (.node u v)) (minimalVertices E (.node u v))) ∧
    (Clear (minimalVertices B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (minimalVertices D (.node u v)) (minimalVertices E (.node u v))) := by
  cases bl : (rootedSpan D u).isEmpty <;> cases br : (rootedSpan D v).isEmpty <;>
    cases cl : (rootedSpan E u).isEmpty <;> cases cr : (rootedSpan E v).isEmpty
  all_goals
    try have nb1 : rootedSpan B l = [] := List.isEmpty_iff.1 (ebl.trans bl)
    try have nb2 : rootedSpan B r = [] := List.isEmpty_iff.1 (ebr.trans br)
    try have nc1 : rootedSpan C l = [] := List.isEmpty_iff.1 (ecl.trans cl)
    try have nc2 : rootedSpan C r = [] := List.isEmpty_iff.1 (ecr.trans cr)
    try have nd1 : rootedSpan D u = [] := List.isEmpty_iff.1 bl
    try have nd2 : rootedSpan D v = [] := List.isEmpty_iff.1 br
    try have ne1 : rootedSpan E u = [] := List.isEmpty_iff.1 cl
    try have ne2 : rootedSpan E v = [] := List.isEmpty_iff.1 cr
    try have mb1 := minimal_nil_of_span_nil B l nb1
    try have mb2 := minimal_nil_of_span_nil B r nb2
    try have mc1 := minimal_nil_of_span_nil C l nc1
    try have mc2 := minimal_nil_of_span_nil C r nc2
    try have md1 := minimal_nil_of_span_nil D u nd1
    try have md2 := minimal_nil_of_span_nil D v nd2
    try have me1 := minimal_nil_of_span_nil E u ne1
    try have me2 := minimal_nil_of_span_nil E v ne2
    simp_all [rootedSpan,minimalVertices,span_root,clear_symm (minimalVertices B l),
      clear_symm (minimalVertices B r),clear_symm (minimalVertices D u),
      clear_symm (minimalVertices D v)]

theorem CherryAt.quotient_geometry {t : Tree} {a b : Nat} {w : Vertex}
    (h : CherryAt a b t w) (z : Nat) (B C : List Nat) (nd : (leaves t).Nodup)
    (hz : z ∉ leaves t) (hzB : z ∉ B) (hzC : z ∉ C)
    (satB : a ∈ B ↔ b ∈ B) (satC : a ∈ C ↔ b ∈ C) :
    (rootedSpan B t).isEmpty = (rootedSpan (contractBlock a b z B) (contract a b z t)).isEmpty ∧
    (rootedSpan C t).isEmpty = (rootedSpan (contractBlock a b z C) (contract a b z t)).isEmpty ∧
    (Clear (rootedSpan B t) (minimalVertices C t) ↔
      Clear (rootedSpan (contractBlock a b z B) (contract a b z t))
        (minimalVertices (contractBlock a b z C) (contract a b z t))) ∧
    (Clear (rootedSpan C t) (minimalVertices B t) ↔
      Clear (rootedSpan (contractBlock a b z C) (contract a b z t))
        (minimalVertices (contractBlock a b z B) (contract a b z t))) ∧
    (Clear (minimalVertices B t) (minimalVertices C t) ↔
      Clear (minimalVertices (contractBlock a b z B) (contract a b z t))
        (minimalVertices (contractBlock a b z C) (contract a b z t))) := by
  induction h with
  | straight =>
    by_cases haB : a ∈ B <;> by_cases haC : a ∈ C
    all_goals have hbB : b ∈ B ↔ a ∈ B := satB.symm
    all_goals have hbC : b ∈ C ↔ a ∈ C := satC.symm
    all_goals simp_all [contract,rootedSpan,minimalVertices,contractBlock_z,prependSide,Clear]
    all_goals exact ⟨[],by simp⟩
  | swapped =>
    by_cases haB : a ∈ B <;> by_cases haC : a ∈ C
    all_goals have hbB : b ∈ B ↔ a ∈ B := satB.symm
    all_goals have hbC : b ∈ C ↔ a ∈ C := satC.symm
    all_goals simp_all [contract,rootedSpan,minimalVertices,contractBlock_z,prependSide,Clear]
    all_goals exact ⟨[],by simp⟩
  | @left l r w h ih =>
    have ndl : (leaves l).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nar := nodup_append_avoid_right l r a nd h.labels.1
    have nbr := nodup_append_avoid_right l r b nd h.labels.2
    have hzl : z ∉ leaves l := fun hx => hz (by simp [leaves,hx])
    have hzr : z ∉ leaves r := fun hx => hz (by simp [leaves,hx])
    have el : ∀ c, l ≠ .leaf c := by intro c he; subst l; cases h
    have cc : contract a b z (.node l r) = .node (contract a b z l) r := by
      simp [contract,el,contract_absent r a b z nar]
    have il := ih ndl hzl
    have irB := geometry_mask_equal r B (contractBlock a b z B)
      (contracted_mask_absent r B a b z nar nbr hzr)
    have irC := geometry_mask_equal r C (contractBlock a b z C)
      (contracted_mask_absent r C a b z nar nbr hzr)
    rw [cc]
    have lift1 := node_quotient_clear_congr l r (contract a b z l) r B C
      (contractBlock a b z B) (contractBlock a b z C) il.1
      (congrArg List.isEmpty irB.1) il.2.1 (congrArg List.isEmpty irC.1)
      il.2.2.1 (by rw [irB.1,irC.2]) il.2.2.2.1 (by rw [irC.1,irB.2])
      il.2.2.2.2 (by rw [irB.2,irC.2])
    have lift2 := node_quotient_clear_congr l r (contract a b z l) r C B
      (contractBlock a b z C) (contractBlock a b z B) il.2.1
      (congrArg List.isEmpty irC.1) il.1 (congrArg List.isEmpty irB.1)
      il.2.2.2.1 (by rw [irC.1,irB.2]) il.2.2.1 (by rw [irB.1,irC.2])
      (by rw [clear_symm,il.2.2.2.2,clear_symm]) (by rw [irC.2,irB.2])
    refine ⟨?_,?_,lift1.1,lift2.1,lift1.2⟩
    · simp only [rootedSpan,il.1,irB.1]; split <;> rfl
    · simp only [rootedSpan,il.2.1,irC.1]; split <;> rfl
  | @right l r w h ih =>
    have ndr : (leaves r).Nodup := List.Sublist.nodup (by simp [leaves]) nd
    have nal := nodup_append_avoid_left l r a nd h.labels.1
    have nbl := nodup_append_avoid_left l r b nd h.labels.2
    have hzl : z ∉ leaves l := fun hx => hz (by simp [leaves,hx])
    have hzr : z ∉ leaves r := fun hx => hz (by simp [leaves,hx])
    have er : ∀ c, r ≠ .leaf c := by intro c he; subst r; cases h
    have cc : contract a b z (.node l r) = .node l (contract a b z r) := by
      simp [contract,er,contract_absent l a b z nal]
    have ir := ih ndr hzr
    have ilB := geometry_mask_equal l B (contractBlock a b z B)
      (contracted_mask_absent l B a b z nal nbl hzl)
    have ilC := geometry_mask_equal l C (contractBlock a b z C)
      (contracted_mask_absent l C a b z nal nbl hzl)
    rw [cc]
    have lift1 := node_quotient_clear_congr l r l (contract a b z r) B C
      (contractBlock a b z B) (contractBlock a b z C) (congrArg List.isEmpty ilB.1)
      ir.1 (congrArg List.isEmpty ilC.1) ir.2.1
      (by rw [ilB.1,ilC.2]) ir.2.2.1 (by rw [ilC.1,ilB.2]) ir.2.2.2.1
      (by rw [ilB.2,ilC.2]) ir.2.2.2.2
    have lift2 := node_quotient_clear_congr l r l (contract a b z r) C B
      (contractBlock a b z C) (contractBlock a b z B) (congrArg List.isEmpty ilC.1)
      ir.2.1 (congrArg List.isEmpty ilB.1) ir.1
      (by rw [ilC.1,ilB.2]) ir.2.2.2.1 (by rw [ilB.1,ilC.2]) ir.2.2.1
      (by rw [ilC.2,ilB.2]) (by rw [clear_symm,ir.2.2.2.2,clear_symm])
    refine ⟨?_,?_,lift1.1,lift2.1,lift1.2⟩
    · simp only [rootedSpan,ilB.1,ir.1]; split <;> rfl
    · simp only [rootedSpan,ilC.1,ir.2.1]; split <;> rfl

end ForestState
