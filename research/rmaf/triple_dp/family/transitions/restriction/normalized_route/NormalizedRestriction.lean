import FamilyTransport
import RestrictionDefs

/-! Concrete normalization premise transport. This module constructs no child
family and claims no transition recovery or graph correspondence. -/
namespace TripleDP.Transitions.Restriction.NormalizedRoute
open TripleDP.Family TripleDP.CostRoute
variable {α I : Type} {l r : BTree α} {k : Nat}

theorem closed_support_exact (F : RawFamily (.node l r) k)
    (hn : (normalize F).openRegion = none) (i : Fin k) :
    (toClosedAssembly (normalize F) hn).support i = (normalize F).closed i := rfl

theorem open_closed_support_exact (F : RawFamily (.node l r) k)
    (R : Support) (hR : (normalize F).openRegion = some R)
    (hl : HasLeaf (.node l r) R) (i : Fin k) :
    (toOpenAssembly (normalize F) R hR hl).support (.inl i) =
      (normalize F).closed i := rfl

theorem open_support_exact (F : RawFamily (.node l r) k)
    (R : Support) (hR : (normalize F).openRegion = some R)
    (hl : HasLeaf (.node l r) R) :
    (toOpenAssembly (normalize F) R hR hl).support (.inr ()) = R := rfl

theorem closed_assembly_openBranchLive (F : RawFamily (.node l r) k)
    (hn : F.openRegion = none) : OpenBranchLive (toClosedAssembly F hn) := by
  intro o ho
  change none = some o at ho
  cases ho

theorem normalized_closed_openBranchLive (F : RawFamily (.node l r) k)
    (hn : (normalize F).openRegion = none) :
    OpenBranchLive (toClosedAssembly (normalize F) hn) :=
  closed_assembly_openBranchLive (normalize F) hn

theorem normalized_open_openBranchLive (F : RawFamily (.node l r) k)
    (R : Support) (hR : (normalize F).openRegion = some R)
    (hl : HasLeaf (.node l r) R) :
    OpenBranchLive (toOpenAssembly (normalize F) R hR hl) := by
  intro o ho side occupied
  change some (Sum.inr ()) = some o at ho
  have he : Sum.inr () = o := Option.some.inj ho
  subst o
  change (∃ a, R (side :: a)) at occupied
  rcases (normalized_open_child_occupied F R hR side).mp occupied with
    ⟨a, ⟨x, hx⟩, ha⟩
  have leaf : LeafAt (.node l r) (side :: a) x :=
    (label_costRoute _ _ _).mp hx
  cases side <;> exact ⟨a, x, leaf, ha⟩

/-- Direct root-path witness proof: a convex root-excluding region's existing
leaf must lie in the same child as every occupied vertex. No least-hull or
normalized-family theorem is used. -/
theorem closed_region_child_live (S : Address → Prop) (convex : PathConvex S)
    (noRoot : ¬ S [])
    (labelled : ∃ a x, LeafAt (.node l r) a x ∧ S a)
    (side : Bool) (occupied : ∃ a, S (side :: a)) :
    ∃ a x, LeafAt (child l r side) a x ∧ S (side :: a) := by
  rcases occupied with ⟨a, ha⟩
  rcases labelled with ⟨b, x, hb, hSb⟩
  cases b with
  | nil => exact False.elim hb
  | cons other rest =>
    have same : side = other := by
      by_cases equal : side = other
      · exact equal
      · have atRoot : OnPath (side :: a) (other :: rest) [] := by
          simp [OnPath, lca, equal]
        exact False.elim (noRoot (convex (side :: a) (other :: rest) ha hSb [] atRoot))
    subst other
    cases side <;> exact ⟨rest, x, hb, hSb⟩

theorem nonboundary_child_live (A : CostRoute.Family (.node l r) I)
    (i : I) (closed : A.boundary ≠ some i) (side : Bool)
    (occupied : ∃ a, A.support i (side :: a)) : Live A side i :=
  closed_region_child_live (A.support i) (A.convex i)
    (fun h => closed ((A.root_spec i).mp h)) (A.labelled i) side occupied

#print axioms closed_support_exact
#print axioms open_closed_support_exact
#print axioms open_support_exact
#print axioms closed_assembly_openBranchLive
#print axioms normalized_closed_openBranchLive
#print axioms normalized_open_openBranchLive
#print axioms closed_region_child_live
#print axioms nonboundary_child_live
end TripleDP.Transitions.Restriction.NormalizedRoute
