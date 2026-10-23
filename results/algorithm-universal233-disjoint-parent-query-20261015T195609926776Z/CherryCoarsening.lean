import CoreGraph

/-! Constructive graph partition coarsening at an actual homogeneous cherry.
The cherry parent may originally be free, in either cherry block, or in a
third block. In the last case its useless pendant excursion is removed from
that third support by the proved one-neighbor walk operation. -/
namespace Universal233.CoreGraph
open RMAF

def mergeOwner (P : SourcePartition t) (a b : Nat) (v : Vertex) : Nat :=
  if P.owner v = b then a else P.owner v

def mergeSupport (P : SourcePartition t) (p : Vertex) (a b i : Nat) (v : Vertex) : Prop :=
  if i = a then v = p ∨ P.support a v ∨ P.support b v
  else if i = b then False
  else P.support i v ∧ v ≠ p

theorem mergeSupport_actual {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) (a b i v) (hv : mergeSupport P p a b i v) : Valid t v := by
  by_cases hi : i = a
  · subst i
    simp only [mergeSupport, if_pos] at hv
    rcases hv with rfl | hv | hv
    · exact cherry_parent_valid h
    · exact P.actual _ _ hv
    · exact P.actual _ _ hv
  · by_cases hj : i = b
    · simp only [mergeSupport, if_neg hi, if_pos hj] at hv
    · have hv' : P.support i v ∧ v ≠ p := by
        simpa only [mergeSupport, if_neg hi, if_neg hj] using hv
      exact P.actual _ _ hv'.1

theorem mergeSupport_terminal {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) (a b : Nat) (hab : a ≠ b)
    (i v z) (hv : LeafAt t v z) :
    mergeSupport P p a b i v ↔ mergeOwner P a b v = i := by
  have hvp := cherry_parent_not_terminal h hv
  have ht : ∀ j, P.support j v ↔ P.owner v = j := fun j => P.terminal_exact j v z hv
  by_cases hi : i = a
  · subst i
    simp only [mergeSupport, if_pos, hvp, false_or, ht, mergeOwner]
    by_cases ho : P.owner v = b
    · simp [ho]
    · simp [ho]
  · by_cases hj : i = b
    · subst i
      simp only [mergeSupport, if_neg (Ne.symm hab), if_pos, mergeOwner]
      by_cases ho : P.owner v = b
      · simp [ho, hab]
      · simp [ho, hvp]
    · simp only [mergeSupport, if_neg hi, if_neg hj, hvp, and_true, ht, mergeOwner]
      by_cases ho : P.owner v = b
      · simp [ho, Ne.symm hi, Ne.symm hj]
      · simp [ho, hvp]

theorem other_cherry_neighbors_unique {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) {i : Nat}
    (hix : i ≠ P.owner (p ++ [false])) (hiy : i ≠ P.owner (p ++ [true])) :
    ∀ u v, Adj t p u → P.support i u → Adj t p v → P.support i v → u = v := by
  have neighbor : ∀ u, Adj t p u → P.support i u → u = p.dropLast := by
    intro u hu hs
    rcases cherry_neighbor_cases h hu with he | he | he
    · subst u
      have heq := (P.terminal_exact _ _ _ (cherry_left h)).mp hs
      exact False.elim (hix heq.symm)
    · subst u
      have heq := (P.terminal_exact _ _ _ (cherry_right h)).mp hs
      exact False.elim (hiy heq.symm)
    · exact he
  intro u v hu hsu hv hsv
  exact (neighbor u hu hsu).trans (neighbor v hv hsv).symm

/-- Every point in the merged support is connected to the actual parent.
This also covers the case where that parent was not in either old support. -/
theorem mergeSupport_from_parent {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) (v : Vertex)
    (hv : mergeSupport P p (P.owner (p ++ [false])) (P.owner (p ++ [true]))
      (P.owner (p ++ [false])) v) :
    Walk t (mergeSupport P p (P.owner (p ++ [false])) (P.owner (p ++ [true]))
      (P.owner (p ++ [false]))) p v := by
  let a := P.owner (p ++ [false])
  let b := P.owner (p ++ [true])
  have parent : mergeSupport P p a b a p := by simp [mergeSupport]
  have left : ∀ w, P.support a w → mergeSupport P p a b a w := by
    intro w hw; simp [mergeSupport, hw]
  have right : ∀ w, P.support b w → mergeSupport P p a b a w := by
    intro w hw; simp [mergeSupport, hw]
  simp only [mergeSupport, if_pos] at hv
  rcases hv with he | hv | hv
  · subst v
    exact .refl parent
  · have edge : Walk t (mergeSupport P p a b a) p (p ++ [false]) :=
      .step parent (cherry_adj_left h) (.refl (left _ (own_terminal P (cherry_left h))))
    exact edge.trans ((P.connected a _ _ (own_terminal P (cherry_left h)) hv).mono left)
  · have edge : Walk t (mergeSupport P p a b a) p (p ++ [true]) :=
      .step parent (cherry_adj_right h) (.refl (right _ (own_terminal P (cherry_right h))))
    exact edge.trans ((P.connected b _ _ (own_terminal P (cherry_right h)) hv).mono right)

theorem mergeSupport_connected {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y)
    (hab : P.owner (p ++ [false]) ≠ P.owner (p ++ [true]))
    (i u v) (hu : mergeSupport P p (P.owner (p ++ [false])) (P.owner (p ++ [true])) i u)
    (hv : mergeSupport P p (P.owner (p ++ [false])) (P.owner (p ++ [true])) i v) :
    Walk t (mergeSupport P p (P.owner (p ++ [false])) (P.owner (p ++ [true])) i) u v := by
  by_cases hi : i = P.owner (p ++ [false])
  · subst i
    exact (mergeSupport_from_parent P h u hu).reverse.trans (mergeSupport_from_parent P h v hv)
  · by_cases hj : i = P.owner (p ++ [true])
    · simp only [mergeSupport, if_neg hi, if_pos hj] at hu
    · have hu' : P.support i u ∧ u ≠ p := by simpa [mergeSupport, hi, hj] using hu
      have hv' : P.support i v ∧ v ≠ p := by simpa [mergeSupport, hi, hj] using hv
      have w := ((P.connected i u v hu'.1 hv'.1).avoid_one_neighbor hv'.2
        (other_cherry_neighbors_unique P h hi hj)).1 hu'.2
      exact w.mono (by intro z hz; simpa [mergeSupport, hi, hj] using hz)

theorem mergeSupport_disjoint {t} (P : SourcePartition t) (p : Vertex) (a b : Nat)
    (hab : a ≠ b) (i j v) (hi : mergeSupport P p a b i v)
    (hj : mergeSupport P p a b j v) : i = j := by
  by_cases hia : i = a
  · subst i
    by_cases hja : j = a
    · exact hja.symm
    · by_cases hjb : j = b
      · simp only [mergeSupport, if_neg hja, if_pos hjb] at hj
      · have hj' : P.support j v ∧ v ≠ p := by simpa [mergeSupport, hja, hjb] using hj
        simp only [mergeSupport, if_pos] at hi
        rcases hi with he | hv | hv
        · exact False.elim (hj'.2 he)
        · exact P.disjoint _ _ _ hv hj'.1
        · exact False.elim (hjb (P.disjoint _ _ _ hj'.1 hv))
  · by_cases hib : i = b
    · simp only [mergeSupport, if_neg hia, if_pos hib] at hi
    · have hi' : P.support i v ∧ v ≠ p := by simpa [mergeSupport, hia, hib] using hi
      by_cases hja : j = a
      · subst j
        simp only [mergeSupport, if_pos] at hj
        rcases hj with he | hv | hv
        · exact False.elim (hi'.2 he)
        · exact P.disjoint _ _ _ hi'.1 hv
        · exact False.elim (hib (P.disjoint _ _ _ hi'.1 hv))
      · by_cases hjb : j = b
        · simp only [mergeSupport, if_neg hja, if_pos hjb] at hj
        · have hj' : P.support j v ∧ v ≠ p := by simpa [mergeSupport, hja, hjb] using hj
          exact P.disjoint _ _ _ hi'.1 hj'.1

/-- Explicit partition surgery. Original labels remain at original addresses;
this is coarsening on the original graph, before contracting the cherry. -/
def coarsenCherry {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y)
    (hab : P.owner (p ++ [false]) ≠ P.owner (p ++ [true])) : SourcePartition t where
  owner := mergeOwner P (P.owner (p ++ [false])) (P.owner (p ++ [true]))
  support := mergeSupport P p (P.owner (p ++ [false])) (P.owner (p ++ [true]))
  actual := mergeSupport_actual P h _ _
  terminal_exact := mergeSupport_terminal P h _ _ hab
  connected := mergeSupport_connected P h hab
  disjoint := mergeSupport_disjoint P p _ _ hab

def Refines {t} (P Q : SourcePartition t) : Prop :=
  ∀ u v x y, LeafAt t u x → LeafAt t v y →
    P.owner u = P.owner v → Q.owner u = Q.owner v

theorem coarsenCherry_refines {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) (hab) : Refines P (coarsenCherry P h hab) := by
  intro u v z w _ _ ho
  change (if P.owner u = P.owner (p ++ [true]) then P.owner (p ++ [false]) else P.owner u) =
    (if P.owner v = P.owner (p ++ [true]) then P.owner (p ++ [false]) else P.owner v)
  rw [ho]

theorem coarsenCherry_same_block {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) (hab) :
    (coarsenCherry P h hab).owner (p ++ [false]) =
      (coarsenCherry P h hab).owner (p ++ [true]) := by
  simp [coarsenCherry, mergeOwner, hab]

theorem coarsenCherry_monochromatic {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) (hab) (color : Nat → Nat)
    (hm : Monochromatic P color) (hc : color x = color y) :
    Monochromatic (coarsenCherry P h hab) color := by
  intro u v z w hu hv he
  let a := P.owner (p ++ [false])
  let b := P.owner (p ++ [true])
  change mergeOwner P a b u = mergeOwner P a b v at he
  by_cases hub : P.owner u = b <;> by_cases hvb : P.owner v = b
  · exact hm _ _ _ _ hu hv (hub.trans hvb.symm)
  · have hva : P.owner v = a := by simpa [mergeOwner, hub, hvb] using he.symm
    exact (hm _ _ _ _ hu (cherry_right h) hub).trans
      (hc.symm.trans (hm _ _ _ _ hv (cherry_left h) hva).symm)
  · have hua : P.owner u = a := by simpa [mergeOwner, hub, hvb] using he
    exact (hm _ _ _ _ hu (cherry_left h) hua).trans
      (hc.trans (hm _ _ _ _ hv (cherry_right h) hvb).symm)
  · exact hm _ _ _ _ hu hv (by simpa [mergeOwner, hub, hvb] using he)

/-- Every valid monochromatic source partition admits a valid monochromatic
coarsening joining a homogeneous cherry. The construction is universal over
actual source graphs and includes a parent occupied by a third block. -/
theorem homogeneous_cherry_coarsening {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) (color : Nat → Nat)
    (hm : Monochromatic P color) (hc : color x = color y) :
    ∃ Q : SourcePartition t, Refines P Q ∧ Monochromatic Q color ∧
      Q.owner (p ++ [false]) = Q.owner (p ++ [true]) := by
  by_cases hab : P.owner (p ++ [false]) = P.owner (p ++ [true])
  · exact ⟨P, (by intro _ _ _ _ _ _ he; exact he), hm, hab⟩
  · exact ⟨coarsenCherry P h hab, coarsenCherry_refines P h hab,
      coarsenCherry_monochromatic P h hab color hm hc, coarsenCherry_same_block P h hab⟩

#print axioms mergeSupport_terminal
#print axioms other_cherry_neighbors_unique
#print axioms mergeSupport_from_parent
#print axioms mergeSupport_connected
#print axioms mergeSupport_disjoint
#print axioms coarsenCherry
#print axioms coarsenCherry_refines
#print axioms coarsenCherry_same_block
#print axioms coarsenCherry_monochromatic
#print axioms homogeneous_cherry_coarsening
end Universal233.CoreGraph
