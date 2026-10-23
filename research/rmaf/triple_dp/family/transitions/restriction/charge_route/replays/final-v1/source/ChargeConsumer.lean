import ChargeCore

namespace TripleDP.RestrictionCharge
open TripleDP.CostRoute

variable {α I : Type}

theorem weight_eq_filter_length (xs : List I) (p : I → Bool) :
    weight xs p = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a <;> simp [weight, bit, List.filter_cons, hp, ih, Nat.add_comm]

theorem boundaryCharge_map {J : Type} (f : I → J) (o : Option I) :
    boundaryCharge (o.map f) = boundaryCharge o := by
  cases o <;> rfl

def projectedRoot {t : BTree α} {live : I → Bool}
    (B : Family t {i // live i = true}) : Option I :=
  B.boundary.map Subtype.val

theorem projected_root_live {t : BTree α} {live : I → Bool}
    (B : Family t {i // live i = true}) (o : I)
    (h : projectedRoot B = some o) : live o = true := by
  cases hb : B.boundary with
  | none => simp [projectedRoot, hb] at h
  | some j =>
    have he : j.val = o := by simpa [projectedRoot, hb] using h
    rw [← he]
    exact j.property

/-- Family.cost is tied to actual enumerated live indices; no count or cost
identity is assumed. The input is equality of concrete enumeration lists. -/
theorem selected_family_cost [DecidableEq I] (enum : FiniteIndex I)
    (live : I → Bool) {t : BTree α} (B : Family t {i // live i = true})
    (enumeration : B.finite.elems.map Subtype.val = enum.elems.filter live) :
    B.cost = closedCharge enum.elems live (projectedRoot B) := by
  have he := congrArg List.length enumeration
  have hw := weight_eq_filter_length enum.elems live
  have hb := close_cost B
  have hc := close_balance enum live (projectedRoot B) (projected_root_live B)
  have hr := boundaryCharge_map Subtype.val B.boundary
  simp only [List.length_map] at he
  change B.cost + boundaryCharge B.boundary = B.finite.elems.length at hb
  change boundaryCharge (projectedRoot B) = boundaryCharge B.boundary at hr
  omega

theorem parent_family_cost [DecidableEq I] {t : BTree α} (A : Family t I) :
    A.cost = closedCharge A.finite.elems (fun _ => true) A.boundary := by
  have hc := close_balance A.finite (fun _ => true) A.boundary (fun _ _ => rfl)
  have hw := weight_true A.finite.elems
  have hp := close_cost A
  change A.cost + boundaryCharge A.boundary = A.finite.elems.length at hp
  omega

/-- Exact support equations plus explicit child-root liveness imply the
precise root indicator. No restriction family is constructed by this lemma. -/
theorem projected_root_spec {l r t : BTree α} (A : Family (.node l r) I)
    (side : Bool) (live : I → Bool) (B : Family t {i // live i = true})
    (support : ∀ j a, B.support j a ↔ A.support j.val (side :: a))
    (rootLive : ∀ i, A.support i [side] → live i = true) (i : I) :
    projectedRoot B = some i ↔ A.support i [side] := by
  constructor
  · intro h
    cases hb : B.boundary with
    | none => simp [projectedRoot, hb] at h
    | some j =>
      have he : j.val = i := by simpa [projectedRoot, hb] using h
      have hs := (support j []).mp ((B.root_spec j).mpr hb)
      simpa [he] using hs
  · intro h
    let j : {i // live i = true} := ⟨i, rootLive i h⟩
    have hb : B.boundary = some j := (B.root_spec j).mp ((support j []).mpr h)
    simp [projectedRoot, hb, j]

/-- Exact conditional consumer for parent/child CostRoute families. All
missing restriction facts are premises: selected index lists, exact supports,
cover, confined overlap, and liveness of occupied child roots. The equations
use child-root support, so a parent-closed owner is still charged correctly. -/
theorem conditional_family_costs [DecidableEq I] {l r : BTree α}
    (A : Family (.node l r) I) (left right : I → Bool)
    (B : Family l {i // left i = true}) (C : Family r {i // right i = true})
    (leftEnumeration : B.finite.elems.map Subtype.val = A.finite.elems.filter left)
    (rightEnumeration : C.finite.elems.map Subtype.val = A.finite.elems.filter right)
    (leftSupport : ∀ j a, B.support j a ↔ A.support j.val (false :: a))
    (rightSupport : ∀ j a, C.support j a ↔ A.support j.val (true :: a))
    (cover : ∀ i, left i = true ∨ right i = true)
    (overlap : ∀ i, left i = true → right i = true → A.boundary = some i)
    (leftRootLive : ∀ i, A.support i [false] → left i = true)
    (rightRootLive : ∀ i, A.support i [true] → right i = true) :
    (A.boundary = none →
      A.cost = B.cost + C.cost + boundaryCharge B.boundary + boundaryCharge C.boundary) ∧
    (∀ o, A.boundary = some o → left o = true → right o = false → A.support o [false] →
      A.cost = B.cost + C.cost + boundaryCharge C.boundary) ∧
    (∀ o, A.boundary = some o → left o = false → right o = true → A.support o [true] →
      A.cost = B.cost + C.cost + boundaryCharge B.boundary) ∧
    (∀ o, A.boundary = some o → left o = true → right o = true →
      A.support o [false] → A.support o [true] → A.cost = B.cost + C.cost) := by
  have h := four_charges A.finite left right A.boundary (projectedRoot B) (projectedRoot C)
    cover overlap (projected_root_live B) (projected_root_live C)
  have ha := parent_family_cost A
  have hb := selected_family_cost A.finite left B leftEnumeration
  have hc := selected_family_cost A.finite right C rightEnumeration
  have hbr := boundaryCharge_map Subtype.val B.boundary
  have hcr := boundaryCharge_map Subtype.val C.boundary
  change boundaryCharge (projectedRoot B) = boundaryCharge B.boundary at hbr
  change boundaryCharge (projectedRoot C) = boundaryCharge C.boundary at hcr
  rw [← ha, ← hb, ← hc, hbr, hcr] at h
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro o hp hl hr hs
    exact h.2.1 o hp hl hr ((projected_root_spec A false left B leftSupport leftRootLive o).mpr hs)
  · intro o hp hl hr hs
    exact h.2.2.1 o hp hl hr ((projected_root_spec A true right C rightSupport rightRootLive o).mpr hs)
  · intro o hp hl hr hsl hsr
    exact h.2.2.2 o hp hl hr
      ((projected_root_spec A false left B leftSupport leftRootLive o).mpr hsl)
      ((projected_root_spec A true right C rightSupport rightRootLive o).mpr hsr)

/-- The actual child block counts follow from their enumerations, not an
assumed target equation. -/
theorem conditional_family_count {l r : BTree α}
    (A : Family (.node l r) I) (left right : I → Bool)
    (B : Family l {i // left i = true}) (C : Family r {i // right i = true})
    (leftEnumeration : B.finite.elems.map Subtype.val = A.finite.elems.filter left)
    (rightEnumeration : C.finite.elems.map Subtype.val = A.finite.elems.filter right)
    (cover : ∀ i, left i = true ∨ right i = true)
    (overlap : ∀ i, left i = true → right i = true → A.boundary = some i) :
    B.blockCount + C.blockCount = A.blockCount + duplicate left right A.boundary := by
  have h := count_balance A.finite left right A.boundary cover overlap
  have hl := congrArg List.length leftEnumeration
  have hr := congrArg List.length rightEnumeration
  simp only [List.length_map] at hl hr
  rw [weight_eq_filter_length, weight_eq_filter_length] at h
  simpa [Family.blockCount, ← hl, ← hr] using h

end TripleDP.RestrictionCharge
