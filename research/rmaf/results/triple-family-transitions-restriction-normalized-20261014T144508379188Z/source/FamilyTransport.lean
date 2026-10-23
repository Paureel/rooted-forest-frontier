import FamilyGeometry
import FamilyAssembly

/-! Exact transport from the raw/retained normalization representation to
the separately authored indexed-family assembly representation. -/
namespace TripleDP.Family

theorem vertex_costRoute (t : BTree α) (v : Address) :
    vertex t v ↔ CostRoute.Vertex t v := by
  induction t generalizing v with
  | leaf x => cases v <;> simp [vertex, CostRoute.Vertex]
  | node l r hl hr =>
      cases v with
      | nil => trivial
      | cons side rest => cases side <;> first | exact hl rest | exact hr rest

theorem label_costRoute (t : BTree α) (v : Address) (x : α) :
    label t v = some x ↔ CostRoute.LeafAt t v x := by
  induction t generalizing v with
  | leaf y => cases v <;> simp [label, CostRoute.LeafAt, eq_comm]
  | node l r hl hr =>
      cases v with
      | nil => simp [label, CostRoute.LeafAt]
      | cons side rest => cases side <;> first | exact hl rest | exact hr rest

def finIndex (k : Nat) : CostRoute.FiniteIndex (Fin k) where
  elems := List.finRange k
  nodup := List.nodup_finRange k
  complete := List.mem_finRange

def unitIndex : CostRoute.FiniteIndex Unit where
  elems := [()]
  nodup := by simp
  complete := by intro u; cases u; simp

def toClosedAssembly (F : RawFamily t k) (hn : F.openRegion = none) :
    CostRoute.Family t (Fin k) where
  finite := finIndex k
  support := F.closed
  bounded := by intro i v hv; exact (vertex_costRoute t v).mp (F.closed_inside i v hv)
  convex := F.closed_convex
  labelled := by
    intro i
    rcases F.closed_live i with ⟨v, ⟨x, hx⟩, hi⟩
    exact ⟨v, x, (label_costRoute t v x).mp hx, hi⟩
  disjoint := F.closed_disjoint
  covers := by
    intro v x hx
    rcases F.covers v ⟨x, (label_costRoute t v x).mpr hx⟩ with hc | ⟨R, hR, _⟩
    · exact hc
    · simp [hn] at hR
  boundary := none
  root_spec := by intro i; simp [F.closed_root i]

def openIndexedSupport (F : RawFamily t k) (R : Support) : Sum (Fin k) Unit → Support
  | .inl i => F.closed i
  | .inr _ => R

def toOpenAssembly (F : RawFamily t k) (R : Support)
    (hR : F.openRegion = some R) (hLive : HasLeaf t R) :
    CostRoute.Family t (Sum (Fin k) Unit) where
  finite := CostRoute.indexSum (finIndex k) unitIndex
  support := openIndexedSupport F R
  bounded := by
    intro i v hv
    cases i with
    | inl i => exact (vertex_costRoute t v).mp (F.closed_inside i v hv)
    | inr u => exact (vertex_costRoute t v).mp (F.open_inside R hR v hv)
  convex := by
    intro i
    cases i with
    | inl i => exact F.closed_convex i
    | inr u => exact F.open_convex R hR
  labelled := by
    intro i
    cases i with
    | inl i =>
        rcases F.closed_live i with ⟨v, ⟨x, hx⟩, hi⟩
        exact ⟨v, x, (label_costRoute t v x).mp hx, hi⟩
    | inr u =>
        rcases hLive with ⟨v, ⟨x, hx⟩, hi⟩
        exact ⟨v, x, (label_costRoute t v x).mp hx, hi⟩
  disjoint := by
    intro i j v hi hj
    cases i with
    | inl i =>
        cases j with
        | inl j => exact congrArg Sum.inl (F.closed_disjoint i j v hi hj)
        | inr u => exact False.elim (F.open_disjoint R hR i v hj hi)
    | inr u =>
        cases j with
        | inl j => exact False.elim (F.open_disjoint R hR j v hi hj)
        | inr w => cases u; cases w; rfl
  covers := by
    intro v x hx
    rcases F.covers v ⟨x, (label_costRoute t v x).mpr hx⟩ with ⟨i, hi⟩ | ⟨Q, hQ, hQv⟩
    · exact ⟨Sum.inl i, hi⟩
    · have he : Q = R := Option.some.inj (hQ.symm.trans hR)
      subst Q
      exact ⟨Sum.inr (), hQv⟩
  boundary := some (.inr ())
  root_spec := by
    intro i
    cases i with
    | inl i => simp [openIndexedSupport, F.closed_root i]
    | inr u => cases u; simp [openIndexedSupport, F.open_root R hR]

theorem toClosedAssembly_count (F : RawFamily t k) (hn : F.openRegion = none) :
    (toClosedAssembly F hn).blockCount = k := by
  simp [CostRoute.Family.blockCount, toClosedAssembly, finIndex]

theorem toClosedAssembly_cost (F : RawFamily t k) (hn : F.openRegion = none) :
    (toClosedAssembly F hn).cost = closedCost F := by
  change (toClosedAssembly F hn).blockCount - 0 = k
  rw [toClosedAssembly_count]
  omega

theorem toOpenAssembly_count (F : RawFamily t k) (R : Support)
    (hR : F.openRegion = some R) (hLive : HasLeaf t R) :
    (toOpenAssembly F R hR hLive).blockCount = k + 1 := by
  simp [CostRoute.Family.blockCount, toOpenAssembly, CostRoute.indexSum, finIndex, unitIndex]

theorem toOpenAssembly_cost (F : RawFamily t k) (R : Support)
    (hR : F.openRegion = some R) (hLive : HasLeaf t R) :
    (toOpenAssembly F R hR hLive).cost = closedCost F := by
  change (toOpenAssembly F R hR hLive).blockCount - 1 = k
  rw [toOpenAssembly_count]
  omega

/-- The normalized family really inhabits the assembly representation, with
the same charged cost and labelled block count. The constructors above retain
each closed support verbatim and, when present, the open support verbatim. -/
theorem normalized_assembly_exists (F : RawFamily t k) :
    ∃ (I : Type) (A : CostRoute.Family t I),
      A.cost = closedCost F ∧ A.blockCount = labelledBlocks F := by
  have hb := normalized_block_charge F
  have hp := normalize_labelled_blocks F
  cases ho : (normalize F).openRegion with
  | none =>
      refine ⟨Fin k, toClosedAssembly (normalize F) ho, ?_, ?_⟩
      · exact (toClosedAssembly_cost _ ho).trans (normalize_closed_cost F)
      · rw [toClosedAssembly_count]
        simp only [closedCost, ho, openCharge, Nat.add_zero] at hb
        omega
  | some R =>
      let live := normalize_retained F R ho
      refine ⟨Sum (Fin k) Unit, toOpenAssembly (normalize F) R ho live, ?_, ?_⟩
      · exact (toOpenAssembly_cost _ R ho live).trans (normalize_closed_cost F)
      · rw [toOpenAssembly_count]
        simp only [closedCost, ho, openCharge] at hb
        omega

#print axioms vertex_costRoute
#print axioms label_costRoute
#print axioms toClosedAssembly
#print axioms toOpenAssembly
#print axioms toClosedAssembly_count
#print axioms toClosedAssembly_cost
#print axioms toOpenAssembly_count
#print axioms toOpenAssembly_cost
#print axioms normalized_assembly_exists
end TripleDP.Family
