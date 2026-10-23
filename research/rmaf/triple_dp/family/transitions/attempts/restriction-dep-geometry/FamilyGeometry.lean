import FamilyTrim
import PathStem

/-! Composed interface: the independently constructed least-convex-hull and
explicit root-path formulations coincide for nonempty leaf supports. These
are integration theorems, not a fresh independent proof lineage. -/
namespace TripleDP.Family

theorem openHull_eq_rootPaths (t : BTree α) (R : Support) (hLive : HasLeaf t R) :
    OpenHull t R = PathRoute.openTrim (Leaf t) R := by
  funext v
  apply propext
  constructor
  · apply hull_least (PathRoute.rootHull_pathConvex (LeafSet t R))
    intro a ha
    rcases ha with ha | rfl
    · exact PathRoute.rootHull_contains_label _ a ha
    · exact (PathRoute.rootHull_root_iff _).mpr hLive
  · exact PathRoute.rootHull_minimal (LeafSet t R) (OpenHull t R)
      (hull_pathConvex _) (hull_contains (Or.inr rfl))
      (fun _ h => hull_contains (Or.inl h)) v

theorem normalized_open_is_rootPaths (F : RawFamily t k) (R : Support)
    (hR : (normalize F).openRegion = some R) :
    R = PathRoute.openTrim (Leaf t) R :=
  (normalized_open_is_hull F R hR).trans
    (openHull_eq_rootPaths t R (normalize_retained F R hR))

theorem normalized_open_child_occupied (F : RawFamily t k) (R : Support)
    (hR : (normalize F).openRegion = some R) (side : Bool) :
    (∃ v, R (side :: v)) ↔ ∃ a, Leaf t (side :: a) ∧ R (side :: a) := by
  have he := normalized_open_is_rootPaths F R hR
  calc
    (∃ v, R (side :: v)) ↔ ∃ v, PathRoute.openTrim (Leaf t) R (side :: v) := by rw [← he]
    _ ↔ ∃ a, Leaf t (side :: a) ∧ R (side :: a) :=
      PathRoute.openTrim_child_occupied_iff _ _ side

theorem normalized_open_no_leafless_child (F : RawFamily t k) (R : Support)
    (hR : (normalize F).openRegion = some R) (side : Bool)
    (hEmpty : ¬ ∃ a, Leaf t (side :: a) ∧ R (side :: a)) :
    ∀ v, ¬ R (side :: v) := by
  intro v hv
  exact hEmpty ((normalized_open_child_occupied F R hR side).mp ⟨v, hv⟩)

theorem closed_leafsets_distinct (F : RawFamily t k) (i j : Fin k)
    (he : LeafSet t (F.closed i) = LeafSet t (F.closed j)) : i = j := by
  rcases F.closed_live i with ⟨v, hv⟩
  have hj : LeafSet t (F.closed j) v := by rw [← he]; exact hv
  exact F.closed_disjoint i j v hv.2 hj.2

theorem closed_leafset_ne_open (F : RawFamily t k) (i : Fin k) (R : Support)
    (hR : F.openRegion = some R) : LeafSet t (F.closed i) ≠ LeafSet t R := by
  intro he
  rcases F.closed_live i with ⟨v, hv⟩
  have hRv : LeafSet t R v := by rw [← he]; exact hv
  exact F.open_disjoint R hR i v hRv.2 hv.2

def openCharge : Option Support → Nat
  | none => 0
  | some _ => 1

theorem normalized_block_charge (F : RawFamily t k) :
    labelledBlocks (normalize F) = closedCost (normalize F) +
      openCharge (normalize F).openRegion := by
  classical
  cases ho : (normalize F).openRegion with
  | none =>
      have hn : ¬ OpenHasLeaf (normalize F) := by simp [OpenHasLeaf, ho]
      simp [labelledBlocks, hn, closedCost, openCharge]
  | some R =>
      have hy : OpenHasLeaf (normalize F) := ⟨R, ho, normalize_retained F R ho⟩
      simp [labelledBlocks, hy, closedCost, openCharge]

theorem normalized_empty_open_pruned (F : RawFamily t k) (R : Support)
    (hR : F.openRegion = some R) (hEmpty : ¬ HasLeaf t R) :
    (normalize F).openRegion = none ∧ closedCost (normalize F) = closedCost F := by
  constructor
  · change trimOpen t F.openRegion = none
    rw [hR]
    exact trimOpen_empty t R hEmpty
  · exact normalize_closed_cost F

#print axioms openHull_eq_rootPaths
#print axioms normalized_open_is_rootPaths
#print axioms normalized_open_child_occupied
#print axioms normalized_open_no_leafless_child
#print axioms closed_leafsets_distinct
#print axioms closed_leafset_ne_open
#print axioms normalized_block_charge
#print axioms normalized_empty_open_pruned
end TripleDP.Family
