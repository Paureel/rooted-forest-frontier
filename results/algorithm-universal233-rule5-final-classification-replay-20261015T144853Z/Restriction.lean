import Endpoint

namespace Universal233.HardParent
open RMAF CoreGraph Integration VertexGeometry

/-- Syntactic rooted cherry, with both sibling orientations admitted. -/
inductive HasCherry (a b : Nat) : Tree → Prop
  | here : HasCherry a b (.node (.leaf a) (.leaf b))
  | swap : HasCherry a b (.node (.leaf b) (.leaf a))
  | left {l r} : HasCherry a b l → HasCherry a b (.node l r)
  | right {l r} : HasCherry a b r → HasCherry a b (.node l r)

theorem hasCherry_labels {a b t} (h : HasCherry a b t) :
    a ∈ leaves t ∧ b ∈ leaves t := by
  induction h with
  | here => simp [leaves]
  | swap => simp [leaves]
  | left h ih => exact ⟨by simp [leaves,ih.1],by simp [leaves,ih.2]⟩
  | right h ih => exact ⟨by simp [leaves,ih.1],by simp [leaves,ih.2]⟩

theorem actual_hasCherry {T p a b} (h : CherryAt T p a b) : HasCherry a b T := by
  induction p generalizing T with
  | nil => simp [CherryAt,subtree] at h; subst T; exact .here
  | cons s p ih =>
    cases T with
    | leaf x => simp [CherryAt,subtree] at h
    | node l r =>
      cases s
      · exact .left (ih h)
      · exact .right (ih h)

theorem iso_hasCherry {u v : Tree} (h : RootedIso u v) {a b : Nat}
    (hc : HasCherry a b u) : HasCherry a b v := by
  induction h with
  | leaf x => cases hc
  | @straight l r u v hl hr ihl ihr =>
    cases hc with
    | here => cases hl; cases hr; exact .here
    | swap => cases hl; cases hr; exact .swap
    | left h => exact .left (ihl h)
    | right h => exact .right (ihr h)
  | @swapped l r u v hl hr ihl ihr =>
    cases hc with
    | here => cases hl; cases hr; exact .swap
    | swap => cases hl; cases hr; exact .here
    | left h => exact .right (ihl h)
    | right h => exact .left (ihr h)

theorem restrict_hasCherry {T a b} (hc : HasCherry a b T) (D : List Nat)
    (ha : a ∈ D) (hb : b ∈ D) :
    ∃ U, restrict D T = some U ∧ HasCherry a b U := by
  induction hc with
  | here => exact ⟨_,by simp [restrict,ha,hb],.here⟩
  | swap => exact ⟨_,by simp [restrict,ha,hb],.swap⟩
  | @left l r hc ih =>
    obtain ⟨U,hU,hcU⟩ := ih
    cases hr : restrict D r with
    | none => exact ⟨U,by simp [restrict,hU,hr],hcU⟩
    | some V => exact ⟨.node U V,by simp [restrict,hU,hr],.left hcU⟩
  | @right l r hc ih =>
    obtain ⟨V,hV,hcV⟩ := ih
    cases hl : restrict D l with
    | none => exact ⟨V,by simp [restrict,hV,hl],hcV⟩
    | some U => exact ⟨.node U V,by simp [restrict,hV,hl],.right hcV⟩

theorem restrict_leaf_filter (D : List Nat) (T : Tree) :
    (restrict D T).map leaves =
      if ((leaves T).filter D.contains).isEmpty then none
      else some ((leaves T).filter D.contains) := by
  induction T with
  | leaf x => simp [restrict,leaves]; split <;> simp_all
  | node l r ihl ihr =>
    cases hl : restrict D l <;> cases hr : restrict D r
    all_goals simp only [hl,hr,Option.map_none,Option.map_some] at ihl ihr
    all_goals simp only [restrict,hl,hr,Option.map_none,Option.map_some,leaves,List.filter_append]
    all_goals split at ihl <;> split at ihr <;> simp_all

theorem restrict_leaves {D : List Nat} {T U : Tree} (h : restrict D T = some U) :
    leaves U = (leaves T).filter D.contains := by
  have hh := restrict_leaf_filter D T
  rw [h] at hh
  simp only [Option.map_some] at hh
  split at hh
  · contradiction
  · exact Option.some.inj hh

theorem restrict_mem {D : List Nat} {T U : Tree} (h : restrict D T = some U) (x : Nat) :
    x ∈ leaves U ↔ x ∈ leaves T ∧ x ∈ D := by
  rw [restrict_leaves h]
  simp

theorem restrict_cherry_from_agreement {T S : Tree} {F : List (List Nat)}
    (ha : agreement T S F = true) {p : RMAF.Vertex} {a b : Nat}
    (hc : CherryAt T p a b) {B : List Nat} (hB : B ∈ F) (haB : a ∈ B) (hbB : b ∈ B) :
    ∃ U, restrict B S = some U ∧ HasCherry a b U := by
  have hall : F.all (restrictionAgrees T S) = true := by
    simp only [agreement,Bool.and_eq_true] at ha
    exact ha.1.1.2
  have hag := (List.all_eq_true.1 hall) B hB
  obtain ⟨V,hV,hcV⟩ := restrict_hasCherry (actual_hasCherry hc) B haB hbB
  cases hU : restrict B S with
  | none => simp [restrictionAgrees,hV,hU] at hag
  | some U =>
    have hi : RootedIso V U := (sameShape_correct V U).1 (by simpa [restrictionAgrees,hV,hU] using hag)
    exact ⟨U,rfl,iso_hasCherry hi hcV⟩
end Universal233.HardParent
