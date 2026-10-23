import ClipCount
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

def isMarker (m : Nat) : Tree → Bool
  | .leaf x => x==m
  | .node _ _ => false

theorem isMarker_true (m : Nat) (t : Tree) (h : isMarker m t=true) : t=.leaf m := by
  cases t with
  | leaf x => have he : x=m := beq_iff_eq.1 h;subst x;rfl
  | node a b => contradiction

theorem isMarker_iso (m : Nat) {t s : Tree} (h : RootedIso t s) : isMarker m t=isMarker m s := by
  cases h <;> rfl

theorem contains_marker_iso (m : Nat) {t s : Tree} (h : RootedIso t s) :
    (leaves t).contains m=(leaves s).contains m := by
  apply Bool.eq_iff_iff.2
  simpa only [List.contains_iff_mem] using BinaryExchange.iso_leaves h m

/-- Suppress repeated marker-only branches along an attachment path. This
total operation is equivariant under rooted isomorphism, even off the common
split regime; no optimum or agreement predicate occurs in its definition. -/
def markerJoin (m : Nat) (l r : Tree) : Tree :=
  if isMarker m l && (leaves r).contains m then r
  else if isMarker m r && (leaves l).contains m then l
  else .node l r

theorem markerJoin_straight (m : Nat) {a b c d : Tree}
    (h : RootedIso a c) (g : RootedIso b d) :
    RootedIso (markerJoin m a b) (markerJoin m c d) := by
  unfold markerJoin
  rw [isMarker_iso m h,isMarker_iso m g,contains_marker_iso m h,contains_marker_iso m g]
  split
  · exact g
  · split
    · exact h
    · exact .straight h g

theorem markerJoin_comm (m : Nat) (a b : Tree) :
    RootedIso (markerJoin m a b) (markerJoin m b a) := by
  cases ha : isMarker m a && (leaves b).contains m <;>
    cases hb : isMarker m b && (leaves a).contains m
  · simp only [markerJoin,ha,hb,Bool.false_eq_true,ite_false]
    exact .swapped (rootedIso_refl a) (rootedIso_refl b)
  · simp only [markerJoin,ha,hb,Bool.false_eq_true,ite_false,ite_true]
    exact rootedIso_refl a
  · simp only [markerJoin,ha,hb,Bool.false_eq_true,ite_false,ite_true]
    exact rootedIso_refl b
  · have haa := ha
    have hbb := hb
    simp only [Bool.and_eq_true] at haa hbb
    have aM : a=.leaf m := isMarker_true m a haa.1
    have bM : b=.leaf m := isMarker_true m b hbb.1
    subst a;subst b
    exact rootedIso_refl _

def contract (Y : List Nat) (m : Nat) : Tree → Tree
  | .leaf x => if Y.contains x then .leaf m else .leaf x
  | .node a b => markerJoin m (contract Y m a) (contract Y m b)

theorem contract_iso (Y : List Nat) (m : Nat) {t s : Tree} (h : RootedIso t s) :
    RootedIso (contract Y m t) (contract Y m s) := by
  induction h with
  | leaf x => exact rootedIso_refl _
  | straight h1 h2 ih1 ih2 => exact markerJoin_straight m ih1 ih2
  | swapped h1 h2 ih1 ih2 =>
    exact rootedIso_trans (markerJoin_straight m ih1 ih2) (markerJoin_comm m _ _)

theorem markerJoin_marker (m : Nat) : markerJoin m (.leaf m) (.leaf m)=.leaf m := by
  simp [markerJoin,isMarker,leaves]

theorem contract_all (Y : List Nat) (m : Nat) (t : Tree) (h : leaves t⊆Y) :
    contract Y m t=.leaf m := by
  induction t with
  | leaf x =>
    have hx : x∈Y := h (by simp [leaves])
    simp [contract,hx]
  | node a b ha hb =>
    have hA : leaves a⊆Y := fun _ hx => h (List.mem_append_left _ hx)
    have hB : leaves b⊆Y := fun _ hx => h (List.mem_append_right _ hx)
    simp only [contract,ha hA,hb hB,markerJoin_marker]

theorem markerJoin_absent (m : Nat) (a b : Tree)
    (ha : m∉leaves a) (hb : m∉leaves b) : markerJoin m a b=.node a b := by
  simp [markerJoin,ha,hb]

theorem contract_none (Y : List Nat) (m : Nat) (t : Tree)
    (h : ∀x∈leaves t,x∉Y) (fresh : m∉leaves t) : contract Y m t=t := by
  induction t with
  | leaf x => simp [contract,h x (by simp [leaves])]
  | node a b ha hb =>
    have hA : ∀x∈leaves a,x∉Y := fun x hx => h x (List.mem_append_left _ hx)
    have hB : ∀x∈leaves b,x∉Y := fun x hx => h x (List.mem_append_right _ hx)
    have fA : m∉leaves a := fun hx => fresh (List.mem_append_left _ hx)
    have fB : m∉leaves b := fun hx => fresh (List.mem_append_right _ hx)
    simp only [contract,ha hA fA,hb hB fB,markerJoin_absent m a b fA fB]
end OrdinaryCommonSplit
