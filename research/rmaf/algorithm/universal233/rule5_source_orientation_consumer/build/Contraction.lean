import SourceBridge
import CherryCoarsening
import CoreInvariants

/-! One-shot original-address graph surgery for homogeneous group contraction.
This module does not assume quotient transport, source coverage or cut realization. -/
namespace Universal233.Integration
open RMAF CoreGraph

/-- Replace one actual cherry by a leaf. Addresses of every surviving vertex
are unchanged; precisely the two old cherry leaves disappear. -/
inductive CherryContraction : Tree → Tree → RMAF.Vertex → Nat → Nat → Nat → Prop
  | root (x y z : Nat) : CherryContraction (.node (.leaf x) (.leaf y)) (.leaf z) [] x y z
  | left {t u p x y z} (r : Tree) : CherryContraction t u p x y z →
      CherryContraction (.node t r) (.node u r) (false :: p) x y z
  | right {t u p x y z} (l : Tree) : CherryContraction t u p x y z →
      CherryContraction (.node l t) (.node l u) (true :: p) x y z

theorem contraction_cherry {t u p x y z} (h : CherryContraction t u p x y z) :
    CherryAt t p x y := by
  induction h with
  | root => rfl
  | left r h ih => exact ih
  | right l h ih => exact ih

theorem contraction_parent {t u p x y z} (h : CherryContraction t u p x y z) :
    LeafAt u p z := by
  induction h with
  | root => rfl
  | left r h ih => exact ih
  | right l h ih => exact ih

theorem contraction_valid {t u p x y z} (h : CherryContraction t u p x y z)
    (v : RMAF.Vertex) :
    Valid u v ↔ Valid t v ∧ v ≠ p ++ [false] ∧ v ≠ p ++ [true] := by
  induction h generalizing v with
  | root x y z =>
    cases v with
    | nil => simp [Valid,subtree]
    | cons s v =>
      cases v with
      | nil => cases s <;> simp [Valid,subtree]
      | cons b v => cases s <;> simp [Valid,subtree]
  | left r h ih =>
    cases v with
    | nil => simp [Valid,subtree]
    | cons s v => cases s <;> simp_all [Valid,subtree]
  | right l h ih =>
    cases v with
    | nil => simp [Valid,subtree]
    | cons s v => cases s <;> simp_all [Valid,subtree]

theorem contraction_terminal {t u p x y z} (h : CherryContraction t u p x y z)
    (v : RMAF.Vertex) (w : Nat) (hv : LeafAt u v w) :
    (v = p ∧ w = z) ∨ LeafAt t v w := by
  induction h generalizing v with
  | root x y z =>
    cases v with
    | nil => exact Or.inl ⟨rfl,by simpa [LeafAt,subtree] using hv.symm⟩
    | cons s v => simp [LeafAt,subtree] at hv
  | left r h ih =>
    cases v with
    | nil => simp [LeafAt,subtree] at hv
    | cons s v =>
      cases s with
      | false =>
        rcases ih v hv with ⟨hp,hw⟩ | hl
        · exact Or.inl ⟨congrArg (false :: ·) hp,hw⟩
        · exact Or.inr hl
      | true => exact Or.inr hv
  | right l h ih =>
    cases v with
    | nil => simp [LeafAt,subtree] at hv
    | cons s v =>
      cases s with
      | false => exact Or.inr hv
      | true =>
        rcases ih v hv with ⟨hp,hw⟩ | hl
        · exact Or.inl ⟨congrArg (true :: ·) hp,hw⟩
        · exact Or.inr hl

theorem adj_subgraph {t u : Tree} {a b : RMAF.Vertex}
    (h : Adj t a b) (ha : Valid u a) (hb : Valid u b) : Adj u a b :=
  ⟨ha,hb,h.2.2⟩

theorem walk_change_tree {t u : Tree} {P : RMAF.Vertex → Prop} {a b : RMAF.Vertex}
    (w : Walk t P a b) (h : ∀ v, P v → Valid u v) : Walk u P a b := by
  induction w with
  | refl hp => exact .refl hp
  | step hp ha tail ih => exact .step hp (adj_subgraph ha (h _ hp) (h _ tail.start)) ih

theorem cherry_children_ne (p : RMAF.Vertex) : p ++ [false] ≠ p ++ [true] := by
  intro h
  have he := List.append_cancel_left h
  cases he

theorem same_block_cherry_parent {t p x y} (P : SourcePartition t)
    (h : CherryAt t p x y) (hs : P.owner (p ++ [false]) = P.owner (p ++ [true])) :
    P.support (P.owner (p ++ [false])) p := by
  have hr := (P.terminal_exact _ _ _ (cherry_right h)).2 hs.symm
  exact walk_from_leaf_visits_parent (cherry_left h)
    (P.connected _ _ _ (own_terminal P (cherry_left h)) hr) (Ne.symm (cherry_children_ne p))

def contractOwner (P : SourcePartition t) (p : RMAF.Vertex) (v : RMAF.Vertex) : Nat :=
  if v = p then P.owner (p ++ [false]) else P.owner v

def contractSupport (P : SourcePartition t) (u : Tree) (i : Nat) (v : RMAF.Vertex) : Prop :=
  P.support i v ∧ Valid u v

theorem contraction_support_connected {t u p x y z} (h : CherryContraction t u p x y z)
    (P : SourcePartition t) (i : Nat) (a b : RMAF.Vertex)
    (ha : contractSupport P u i a) (hb : contractSupport P u i b) :
    Walk u (contractSupport P u i) a b := by
  have ca := (contraction_valid h a).1 ha.2
  have cb := (contraction_valid h b).1 hb.2
  have hch := contraction_cherry h
  have uniqueL : ∀ v w, Adj t (p ++ [false]) v → P.support i v →
      Adj t (p ++ [false]) w → P.support i w → v = w := by
    intro v w hv _ hw _
    exact (leaf_neighbor_parent (cherry_left hch) hv).trans
      (leaf_neighbor_parent (cherry_left hch) hw).symm
  have uniqueR : ∀ v w, Adj t (p ++ [true]) v → (P.support i v ∧ v ≠ p ++ [false]) →
      Adj t (p ++ [true]) w → (P.support i w ∧ w ≠ p ++ [false]) → v = w := by
    intro v w hv _ hw _
    exact (leaf_neighbor_parent (cherry_right hch) hv).trans
      (leaf_neighbor_parent (cherry_right hch) hw).symm
  have w1 := ((P.connected i a b ha.1 hb.1).avoid_one_neighbor cb.2.1 uniqueL).1 ca.2.1
  have w2 := (w1.avoid_one_neighbor cb.2.2 uniqueR).1 ca.2.2
  have w3 : Walk t (contractSupport P u i) a b := w2.mono (by
    intro v hv
    exact ⟨hv.1.1,(contraction_valid h v).2 ⟨P.actual _ _ hv.1.1,hv.1.2,hv.2⟩⟩)
  exact walk_change_tree w3 (fun v hv => hv.2)

/-- Actual graph quotient at one homogeneous cherry after coarsening. -/
def contractPartition {t u p x y z} (h : CherryContraction t u p x y z)
    (P : SourcePartition t) (hs : P.owner (p ++ [false]) = P.owner (p ++ [true])) :
    SourcePartition u where
  owner := contractOwner P p
  support := contractSupport P u
  actual := by intro i v hv; exact hv.2
  terminal_exact := by
    intro i v w hv
    rcases contraction_terminal h v w hv with ⟨hvp,hw⟩ | ht
    · subst v
      have hp := same_block_cherry_parent P (contraction_cherry h) hs
      have he : P.support i p ↔ P.owner (p ++ [false]) = i := by
        constructor
        · intro hi; exact P.disjoint _ _ _ hp hi
        · intro hi; simpa [hi] using hp
      simp only [contractSupport,contractOwner]
      exact ⟨fun hi => he.1 hi.1,fun hi => ⟨he.2 hi,hv.valid⟩⟩
    · have hn := cherry_parent_not_terminal (contraction_cherry h) ht
      simp only [contractSupport,contractOwner,ite_eq_right hn]
      exact ⟨fun hi => (P.terminal_exact i v w ht).1 hi.1,
        fun hi => ⟨(P.terminal_exact i v w ht).2 hi,hv.valid⟩⟩
  connected := contraction_support_connected h P
  disjoint := by intro i j v hi hj; exact P.disjoint _ _ _ hi.1 hj.1

def cherryProjection (p v : RMAF.Vertex) : RMAF.Vertex :=
  if v = p ++ [false] ∨ v = p ++ [true] then p else v

/-- Exact owner lift for every original leaf occurrence, including both deleted
cherry terminals. This preserves original blocks through the quotient. -/
theorem contractPartition_owner {t u p x y z} (h : CherryContraction t u p x y z)
    (P : SourcePartition t) (hs : P.owner (p ++ [false]) = P.owner (p ++ [true]))
    (v : RMAF.Vertex) (w : Nat) (hv : LeafAt t v w) :
    (contractPartition h P hs).owner (cherryProjection p v) = P.owner v := by
  change contractOwner P p (cherryProjection p v) = P.owner v
  unfold cherryProjection
  split
  next hh =>
    rcases hh with rfl | rfl
    · simp [contractOwner]
    · simpa [contractOwner] using hs
  next hh =>
    have hn := cherry_parent_not_terminal (contraction_cherry h) hv
    simp [contractOwner,hn]

theorem contractPartition_monochromatic {t u p x y z}
    (h : CherryContraction t u p x y z) (P : SourcePartition t)
    (hs : P.owner (p ++ [false]) = P.owner (p ++ [true]))
    (color : Nat → Nat) (hm : Monochromatic P color) (hz : color z = color x) :
    Monochromatic (contractPartition h P hs) color := by
  intro a b va vb ha hb ho
  have hat := contraction_terminal h a va ha
  have hbt := contraction_terminal h b vb hb
  rcases hat with ⟨hap,hva⟩ | hat
  · subst a; subst va
    rcases hbt with ⟨hbp,hvb⟩ | hbt
    · subst b; subst vb; rfl
    · have hbn := cherry_parent_not_terminal (contraction_cherry h) hbt
      have he : P.owner (p ++ [false]) = P.owner b := by simpa [contractPartition,contractOwner,hbn] using ho
      exact hz.trans (hm _ _ _ _ (cherry_left (contraction_cherry h)) hbt he)
  · rcases hbt with ⟨hbp,hvb⟩ | hbt
    · subst b; subst vb
      have han := cherry_parent_not_terminal (contraction_cherry h) hat
      have he : P.owner a = P.owner (p ++ [false]) := by simpa [contractPartition,contractOwner,han] using ho
      exact (hm _ _ _ _ hat (cherry_left (contraction_cherry h)) he).trans hz.symm
    · have han := cherry_parent_not_terminal (contraction_cherry h) hat
      have hbn := cherry_parent_not_terminal (contraction_cherry h) hbt
      exact hm _ _ _ _ hat hbt (by simpa [contractPartition,contractOwner,han,hbn] using ho)

end Universal233.Integration
