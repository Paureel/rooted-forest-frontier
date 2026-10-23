/- Independent restriction transport under fresh cherry expansion. -/
import ExpansionPartitionV2
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

inductive Grow (a b z : Nat) : Tree → Tree → Prop where
 | fixed {x} : x≠a → x≠b → x≠z → Grow a b z (.leaf x) (.leaf x)
 | cherry : Grow a b z (.leaf z) (.node (.leaf a) (.leaf b))
 | swapped : Grow a b z (.leaf z) (.node (.leaf b) (.leaf a))
 | node {l r L R} : Grow a b z l L → Grow a b z r R → Grow a b z (.node l r) (.node L R)

inductive MaybeGrow (a b z : Nat) : Option Tree → Option Tree → Prop where
 | none : MaybeGrow a b z none none
 | some {C T} : Grow a b z C T → MaybeGrow a b z (some C) (some T)

theorem expand_membership (B : List Nat) (a b z x : Nat) :
 x∈expandBlock a b z B ↔ (x∈B ∧ x≠z) ∨ (z∈B ∧ (x=a ∨ x=b)) := by
 induction B with
 | nil => simp [expandBlock]
 | cons y ys ih =>
  by_cases yz : y=z
  · subst y; simp [expandBlock,ih]; tauto
  · simp [expandBlock,yz,ih]; tauto

theorem endpoint_contains (B : List Nat) (a b z : Nat) (na : a∉B) (nb : b∉B) :
 (expandBlock a b z B).contains a=B.contains z ∧
 (expandBlock a b z B).contains b=B.contains z := by
 constructor <;> apply Bool.eq_iff_iff.2 <;>
  simp only [List.contains_iff,expand_membership] <;> simp_all

theorem fixed_contains (B : List Nat) {a b z x : Nat}
 (xa : x≠a) (xb : x≠b) (xz : x≠z) :
 (expandBlock a b z B).contains x=B.contains x := by
 apply Bool.eq_iff_iff.2
 simp only [List.contains_iff,expand_membership]
 simp [xa,xb,xz]

theorem restrict_grow {a b z : Nat} {C T : Tree} (h : Grow a b z C T)
 (B : List Nat) (na : a∉B) (nb : b∉B) :
 MaybeGrow a b z (restrict B C) (restrict (expandBlock a b z B) T) := by
 induction h with
 | fixed xa xb xz =>
  simp only [restrict,fixed_contains B xa xb xz]
  split
  · exact .some (.fixed xa xb xz)
  · exact .none
 | cherry =>
  have ep := endpoint_contains B a b z na nb
  simp only [restrict,ep.1,ep.2]
  split
  · exact .some .cherry
  · exact .none
 | swapped =>
  have ep := endpoint_contains B a b z na nb
  simp only [restrict,ep.1,ep.2]
  split
  · exact .some .swapped
  · exact .none
 | node hl hr il ir =>
  cases il <;> cases ir <;> simp only [restrict] <;> simp_all only
  · exact .none
  · exact .some (by assumption)
  · exact .some (by assumption)
  · exact .some (.node (by assumption) (by assumption))

theorem iso_refl (T : Tree) : RootedIso T T := by
 induction T with
 | leaf x => exact .leaf x
 | node l r il ir => exact .straight il ir

theorem grow_iso {a b z : Nat} {C D T U : Tree} (iso : RootedIso C D)
 (gt : Grow a b z C T) (gu : Grow a b z D U) : RootedIso T U := by
 induction iso generalizing T U with
 | leaf x =>
  cases gt <;> cases gu
  all_goals first
   | exact .leaf _
   | exact iso_refl _
   | exact .swapped (.leaf _) (.leaf _)
   | contradiction
 | straight hl hr il ir =>
  cases gt with
  | node gl gr =>
   cases gu with
   | node ul ur => exact .straight (il gl ul) (ir gr ur)
 | swapped hl hr il ir =>
  cases gt with
  | node gl gr =>
   cases gu with
   | node ul ur => exact .swapped (il gl ur) (ir gr ul)

theorem same_iso {T U : Tree} (h : sameShape T U=true) : RootedIso T U := by
 induction T generalizing U with
 | leaf x =>
  cases U with
  | leaf y => have e : x=y := by simpa [sameShape] using h; subst y; exact .leaf x
  | node l r => simp [sameShape] at h
 | node l r il ir =>
  cases U with
  | leaf y => simp [sameShape] at h
  | node u v =>
   simp only [sameShape,Bool.or_eq_true,Bool.and_eq_true] at h
   rcases h with h|h
   · exact .straight (il h.1) (ir h.2)
   · exact .swapped (il h.1) (ir h.2)

theorem iso_same {T U : Tree} (h : RootedIso T U) : sameShape T U=true := by
 induction h with
 | leaf x => simp [sameShape]
 | straight hl hr il ir => simp [sameShape,il,ir]
 | swapped hl hr il ir => simp [sameShape,il,ir]

theorem restriction_agrees_grow {a b z : Nat} {C D T U : Tree}
 (gt : Grow a b z C T) (gu : Grow a b z D U)
 (B : List Nat) (na : a∉B) (nb : b∉B)
 (h : restrictionAgrees C D B=true) :
 restrictionAgrees T U (expandBlock a b z B)=true := by
 have left := restrict_grow gt B na nb
 have right := restrict_grow gu B na nb
 cases left with
 | none => simp [restrictionAgrees] at h
 | @some c t ht =>
  cases right with
  | none => simp [restrictionAgrees] at h
  | @some d u hu =>
   exact iso_same (grow_iso (same_iso h) ht hu)
end IndependentGeometry
