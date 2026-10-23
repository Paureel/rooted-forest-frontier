import FamilyTrim

namespace TripleDP.Family.Controls

def rootOnly : Support := fun v => v = []

theorem rootOnly_convex : PathConvex rootOnly := by
  apply (rooted_pathConvex_iff_prefixClosed rootOnly rfl).mpr
  intro a ha p hp
  change a = [] at ha
  subst a
  exact List.prefix_nil.mp hp

def singletonFamily : RawFamily (.leaf 0) 0 where
  closed := fun i => Fin.elim0 i
  openRegion := some rootOnly
  closed_convex := fun i => Fin.elim0 i
  closed_inside := fun i => Fin.elim0 i
  closed_live := fun i => Fin.elim0 i
  closed_root := fun i => Fin.elim0 i
  closed_disjoint := fun i => Fin.elim0 i
  open_convex := by
    intro R hR
    have he := Option.some.inj hR
    subst R
    exact rootOnly_convex
  open_inside := by
    intro R hR v hv
    have he := Option.some.inj hR
    subst R
    change v = [] at hv
    subst v
    trivial
  open_root := by
    intro R hR
    have he := Option.some.inj hR
    subst R
    rfl
  open_disjoint := by
    intro R hR i
    exact Fin.elim0 i
  covers := by
    intro v hv
    cases v with
    | nil => exact Or.inr ⟨rootOnly, rfl, rfl⟩
    | cons side rest => simp [Leaf, label] at hv

theorem singleton_cost_clean : closedCost (normalize singletonFamily) = 0 := rfl

theorem singleton_retained_clean : Retained (normalize singletonFamily) :=
  normalize_retained singletonFamily

theorem singleton_root_survives :
    ∃ R, (normalize singletonFamily).openRegion = some R ∧ R [] := by
  apply (normalize_open_labels singletonFamily [] ⟨0, rfl⟩).mpr
  exact ⟨rootOnly, rfl, rfl⟩

theorem empty_open_discarded (t : BTree α) (R : Support) (h : ¬ HasLeaf t R) :
    trimOpen t (some R) = none := trimOpen_empty t R h

#print axioms singleton_cost_clean
#print axioms singleton_retained_clean
#print axioms singleton_root_survives
#print axioms empty_open_discarded
end TripleDP.Family.Controls
