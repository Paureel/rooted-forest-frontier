import Std

/-! One-shot proof artifact for the universal233 graph consumer. Addresses are
vertices of the unsuppressed binary tree. No abstract coverage field is used
for the graph claims. Original RMAF executable semantics is imported below
by the separate bridge module. -/
namespace VertexGeometry
abbrev Vertex := List Bool

/-- The unique path in the infinite binary address tree, with endpoints kept.
Its restriction to a prefix-closed finite binary tree is its actual graph path. -/
inductive PathAt : Vertex → Vertex → Vertex → Prop where
  | endpointL (a b : Vertex) : PathAt a a b
  | endpointR (a b : Vertex) : PathAt b a b
  | fork (a b : Vertex) : PathAt [] (false :: a) (true :: b)
  | fork' (a b : Vertex) : PathAt [] (true :: a) (false :: b)
  | down (s : Bool) {v a b : Vertex} : PathAt v a b → PathAt (s :: v) (s :: a) (s :: b)
  | leftLeg (s : Bool) {v a : Vertex} : PathAt v a [] → PathAt (s :: v) (s :: a) []
  | rightLeg (s : Bool) {v b : Vertex} : PathAt v [] b → PathAt (s :: v) [] (s :: b)
  | crossLeft (s : Bool) {v a b : Vertex} : PathAt v a [] →
      PathAt (s :: v) (s :: a) ((!s) :: b)
  | crossRight (s : Bool) {v a b : Vertex} : PathAt v [] b →
      PathAt (s :: v) ((!s) :: a) (s :: b)

/-- Leaf-address hull, including singleton leaf hulls. -/
def Hull (S : Vertex → Prop) (v : Vertex) : Prop :=
  ∃ a b, S a ∧ S b ∧ PathAt v a b

def Prefix (p a : Vertex) : Prop := ∃ q, a = p ++ q

def ProperPrefix (p a : Vertex) : Prop := ∃ s q, a = p ++ s :: q

/-- Removing a nonlabelled target gives the parent direction and two child
regions. The value 3 is the removed vertex itself, never a label in our use. -/
def region : Vertex → Vertex → Nat
  | [], [] => 3
  | [], false :: _ => 0
  | [], true :: _ => 1
  | _ :: _, [] => 2
  | s :: v, t :: a => if s = t then region v a else 2

/-- At two surviving vertices, equality means membership in the same actual
component after deleting the target. -/
def SameRegion (v a b : Vertex) : Prop := region v a = region v b

-- The strengthened statement is deliberately false when labels may equal v.
theorem singleton_occupies (a : Vertex) : Hull (fun b => b = a) a :=
  ⟨a, a, rfl, rfl, PathAt.endpointL a a⟩

theorem region_self (a : Vertex) : region a a = 3 := by
  induction a with
  | nil => rfl
  | cons s a ih => simpa [region] using ih

theorem region_root_not_up (a : Vertex) : region [] a ≠ 2 := by
  cases a with
  | nil => decide
  | cons s a => cases s <;> simp [region]

theorem path_to_root_not_up (v a b : Vertex) (h : PathAt v a b)
    (hb : b = []) : region v a ≠ 2 := by
  induction h with
  | endpointL a b => simp [region_self]
  | endpointR a b => subst b; exact region_root_not_up a
  | fork a b => contradiction
  | fork' a b => contradiction
  | down s h ih => contradiction
  | leftLeg s h ih => simpa [region] using ih rfl
  | rightLeg s h ih => contradiction
  | crossLeft s h ih => contradiction
  | crossRight s h ih => contradiction

theorem path_from_root_not_up (v a b : Vertex) (h : PathAt v a b)
    (ha : a = []) : region v b ≠ 2 := by
  induction h with
  | endpointL a b => subst a; exact region_root_not_up b
  | endpointR a b => simp [region_self]
  | fork a b => contradiction
  | fork' a b => contradiction
  | down s h ih => contradiction
  | leftLeg s h ih => contradiction
  | rightLeg s h ih => simpa [region] using ih rfl
  | crossLeft s h ih => contradiction
  | crossRight s h ih => contradiction

/-- Every path through a nonendpoint crosses distinct actual directions. -/
theorem path_region_ne (v a b : Vertex) (h : PathAt v a b)
    (ha : a ≠ v) (hb : b ≠ v) : region v a ≠ region v b := by
  induction h with
  | endpointL a b => exact False.elim (ha rfl)
  | endpointR a b => exact False.elim (hb rfl)
  | fork a b => simp [region]
  | fork' a b => simp [region]
  | @down s v a b h ih =>
      have hna : a ≠ v := by intro e; exact ha (congrArg (s :: ·) e)
      have hnb : b ≠ v := by intro e; exact hb (congrArg (s :: ·) e)
      simpa [region] using ih hna hnb
  | @leftLeg s v a h ih =>
      simpa [region] using path_to_root_not_up v a [] h rfl
  | @rightLeg s v b h ih =>
      simpa [region, ne_comm] using path_from_root_not_up v [] b h rfl
  | @crossLeft s v a b h ih =>
      cases s <;> simpa [region] using path_to_root_not_up v a [] h rfl
  | @crossRight s v a b h ih =>
      cases s <;> simpa [region, ne_comm] using path_from_root_not_up v [] b h rfl

theorem path_sym {v a b : Vertex} (h : PathAt v a b) : PathAt v b a := by
  induction h with
  | endpointL a b => exact PathAt.endpointR b a
  | endpointR a b => exact PathAt.endpointL b a
  | fork a b => exact PathAt.fork' b a
  | fork' a b => exact PathAt.fork b a
  | down s h ih => exact PathAt.down s ih
  | leftLeg s h ih => exact PathAt.rightLeg s ih
  | rightLeg s h ih => exact PathAt.leftLeg s ih
  | crossLeft s h ih => exact PathAt.crossRight s ih
  | crossRight s h ih => exact PathAt.crossLeft s ih

theorem not_up_path_to_root (v a : Vertex) (h : region v a ≠ 2) :
    PathAt v a [] := by
  induction v generalizing a with
  | nil => exact PathAt.endpointR a []
  | cons s v ih =>
    cases a with
    | nil => exact False.elim (h rfl)
    | cons t a =>
      by_cases e : s = t
      · subst t
        exact PathAt.leftLeg s (ih a (by simpa [region] using h))
      · exact False.elim (h (by simp [region, e]))

theorem region_ne_path (v a b : Vertex) (h : region v a ≠ region v b) :
    PathAt v a b := by
  induction v generalizing a b with
  | nil =>
    cases a with
    | nil => exact PathAt.endpointL [] b
    | cons s a =>
      cases b with
      | nil => exact PathAt.endpointR (s :: a) []
      | cons t b =>
        cases s <;> cases t
        · exact False.elim (h rfl)
        · exact PathAt.fork a b
        · exact PathAt.fork' a b
        · exact False.elim (h rfl)
  | cons s v ih =>
    cases a with
    | nil =>
      cases b with
      | nil => exact False.elim (h rfl)
      | cons t b =>
        by_cases e : s = t
        · subst t
          apply PathAt.rightLeg s
          apply path_sym
          apply not_up_path_to_root
          simpa [region, ne_comm] using h
        · exact False.elim (h (by simp [region, e]))
    | cons t a =>
      cases b with
      | nil =>
        by_cases e : s = t
        · subst t
          apply PathAt.leftLeg s
          apply not_up_path_to_root
          simpa [region] using h
        · exact False.elim (h (by simp [region, e]))
      | cons u b =>
        by_cases e : s = t
        · subst t
          by_cases f : s = u
          · subst u
            apply PathAt.down s
            exact ih a b (by simpa [region] using h)
          · have hu : u = !s := by cases s <;> cases u <;> simp_all
            subst u
            apply PathAt.crossLeft s
            apply not_up_path_to_root
            cases s <;> simpa [region] using h
        · by_cases f : s = u
          · subst u
            have ht : t = !s := by cases s <;> cases t <;> simp_all
            subst t
            apply PathAt.crossRight s
            apply path_sym
            apply not_up_path_to_root
            cases s <;> simpa [region, ne_comm] using h
          · exact False.elim (h (by simp [region, e, f]))

/-- Exact avoiding-region equivalence in the actual unsuppressed address graph.
The no-target-label hypothesis is essential even for singleton pieces. -/
theorem avoids_iff_monochromatic (S : Vertex → Prop) (v : Vertex)
    (hlabel : ¬S v) :
    (¬Hull S v) ↔ (∀ a b, S a → S b → SameRegion v a b) := by
  constructor
  · intro h a b ha hb
    by_cases heq : region v a = region v b
    · exact heq
    · exact False.elim (h ⟨a, b, ha, hb, region_ne_path v a b heq⟩)
  · intro h ⟨a, b, ha, hb, hp⟩
    exact path_region_ne v a b hp (by intro e; subst a; exact hlabel ha)
      (by intro e; subst b; exact hlabel hb) (h a b ha hb)

theorem region_eq_three_iff (v a : Vertex) : region v a = 3 ↔ a = v := by
  induction v generalizing a with
  | nil => cases a with
    | nil => simp [region]
    | cons s a => cases s <;> simp [region]
  | cons s v ih =>
    cases a with
    | nil => simp [region]
    | cons t a =>
      by_cases e : s = t
      · subst t; simpa [region] using ih a
      · simp [region, e, Ne.symm e]

theorem region_le_three (v a : Vertex) : region v a ≤ 3 := by
  induction v generalizing a with
  | nil => cases a with
    | nil => decide
    | cons s a => cases s <;> simp [region]
  | cons s v ih =>
    cases a with
    | nil => simp [region]
    | cons t a =>
      by_cases e : s = t
      · simpa [region, e] using ih a
      · simp [region, e]

theorem nonlabel_region_lt_three (v a : Vertex) (h : a ≠ v) : region v a < 3 := by
  have hle := region_le_three v a
  have hne : region v a ≠ 3 := by simpa [region_eq_three_iff] using h
  omega

/-- An occupied nonlabelled span has at least two nonempty directions, and
all such directions are among 0, 1, 2. This excludes r < 2 and r > 3. -/
theorem occupied_nonlabel_two_directions (S : Vertex → Prop) (v : Vertex)
    (hlabel : ¬S v) (h : Hull S v) :
    ∃ a b, S a ∧ S b ∧ region v a < 3 ∧ region v b < 3 ∧
      region v a ≠ region v b := by
  rcases h with ⟨a,b,ha,hb,hp⟩
  have hna : a ≠ v := by intro e; subst a; exact hlabel ha
  have hnb : b ≠ v := by intro e; subst b; exact hlabel hb
  exact ⟨a,b,ha,hb,nonlabel_region_lt_three v a hna,
    nonlabel_region_lt_three v b hnb,path_region_ne v a b hp hna hnb⟩

/-- Complete component signature for deleting both targets. Equality in both
coordinates says exactly that the unique address path avoids both vertices. -/
def jointRegion (v w a : Vertex) : Nat × Nat := (region v a, region w a)

def TwoJointRegions (S : Vertex → Prop) (v w : Vertex) : Prop :=
  ∃ a b, S a ∧ S b ∧ jointRegion v w a ≠ jointRegion v w b ∧
    ∀ x, S x → jointRegion v w x = jointRegion v w a ∨
      jointRegion v w x = jointRegion v w b

/-- Exactly two nonempty joint regions and occupancy of both targets force
both individual separators to distinguish those same two regions. -/
theorem two_joint_coordinate_separation (S : Vertex → Prop) (v w a b : Vertex)
    (hlabelv : ¬S v) (hlabelw : ¬S w)
    (hv : Hull S v) (hw : Hull S w)
    (hcover : ∀ x, S x → jointRegion v w x = jointRegion v w a ∨
      jointRegion v w x = jointRegion v w b) :
    region v a ≠ region v b ∧ region w a ≠ region w b := by
  have first : ∀ z, (∀ x, S x → jointRegion v w x = jointRegion v w a ∨
      jointRegion v w x = jointRegion v w b) →
      (z = v ∨ z = w) → (¬S z) → Hull S z → region z a ≠ region z b := by
    intro z hc hz hlabel hocc heq
    apply (avoids_iff_monochromatic S z hlabel).2 _ hocc
    intro x y hx hy
    rcases hc x hx with hxa | hxb <;> rcases hc y hy with hya | hyb
    all_goals
      cases hz with
      | inl e =>
        subst z
        have hxx := congrArg Prod.fst (by assumption : jointRegion v w x = _)
        have hyy := congrArg Prod.fst (by assumption : jointRegion v w y = _)
        simp only [jointRegion] at hxx hyy
        unfold SameRegion
        omega
      | inr e =>
        subst z
        have hxx := congrArg Prod.snd (by assumption : jointRegion v w x = _)
        have hyy := congrArg Prod.snd (by assumption : jointRegion v w y = _)
        simp only [jointRegion] at hxx hyy
        unfold SameRegion
        omega
  exact ⟨first v hcover (Or.inl rfl) hlabelv hv,
    first w hcover (Or.inr rfl) hlabelw hw⟩

theorem two_joint_same_separator (S : Vertex → Prop) (v w : Vertex)
    (hlabelv : ¬S v) (hlabelw : ¬S w)
    (hv : Hull S v) (hw : Hull S w) (hr : TwoJointRegions S v w) :
    ∀ x y, S x → S y → (SameRegion v x y ↔ SameRegion w x y) := by
  rcases hr with ⟨a,b,ha,hb,hab,hcover⟩
  obtain ⟨hva,hwa⟩ := two_joint_coordinate_separation S v w a b hlabelv hlabelw hv hw hcover
  intro x y hx hy
  rcases hcover x hx with hxa | hxb <;> rcases hcover y hy with hya | hyb
  all_goals
    have hxx := congrArg Prod.fst (by assumption : jointRegion v w x = _)
    have hyy := congrArg Prod.fst (by assumption : jointRegion v w y = _)
    have gxx := congrArg Prod.snd (by assumption : jointRegion v w x = _)
    have gyy := congrArg Prod.snd (by assumption : jointRegion v w y = _)
    simp only [jointRegion] at hxx hyy gxx gyy
    unfold SameRegion
    omega

/-- The chain's leafless-middle case: EVERY subset piece of B occupies v iff
it occupies w. No second cut to the same parent has been charged. -/
theorem two_region_coincident_occupancy (S P : Vertex → Prop) (v w : Vertex)
    (hlabelv : ¬S v) (hlabelw : ¬S w)
    (hv : Hull S v) (hw : Hull S w) (hr : TwoJointRegions S v w)
    (hsub : ∀ a, P a → S a) : Hull P v ↔ Hull P w := by
  classical
  have hmono := two_joint_same_separator S v w hlabelv hlabelw hv hw hr
  have hpv : ¬P v := fun h => hlabelv (hsub v h)
  have hpw : ¬P w := fun h => hlabelw (hsub w h)
  constructor
  · intro hp
    by_cases hh : Hull P w
    · exact hh
    · exact False.elim ((avoids_iff_monochromatic P v hpv).2
        (fun a b ha hb => (hmono a b (hsub a ha) (hsub b hb)).2
          ((avoids_iff_monochromatic P w hpw).1 hh a b ha hb)) hp)
  · intro hp
    by_cases hh : Hull P v
    · exact hh
    · exact False.elim ((avoids_iff_monochromatic P w hpw).2
        (fun a b ha hb => (hmono a b (hsub a ha) (hsub b hb)).1
          ((avoids_iff_monochromatic P v hpv).1 hh a b ha hb)) hp)

/-- Rooted ownership uses actual final-piece hulls, not the whole parent span. -/
def Occupies (F : Nat → List (Vertex → Prop)) (i : Nat) (v : Vertex) : Prop :=
  ∃ P, P ∈ F i ∧ Hull P v

def Clear (F : Nat → List (Vertex → Prop)) (i : Nat) (v : Vertex) : Prop :=
  ¬Occupies F i v

/-- At most one parent can own a fixed vertex in a final disjoint agreement
partition. Pairwise disjointness of final pieces is the exact premise. -/
def DisjointParents (F : Nat → List (Vertex → Prop)) : Prop :=
  ∀ i j, i ≠ j → ∀ P, P ∈ F i → ∀ Q, Q ∈ F j →
    ∀ v, ¬(Hull P v ∧ Hull Q v)

theorem distinct_parents_no_joint_owner (F : Nat → List (Vertex → Prop))
    (hd : DisjointParents F) (i j : Nat) (hij : i ≠ j) (v : Vertex) :
    ¬(Occupies F i v ∧ Occupies F j v) := by
  rintro ⟨⟨P,hP,hPv⟩,⟨Q,hQ,hQv⟩⟩
  exact hd i j hij P hP Q hQ v ⟨hPv,hQv⟩

theorem clique_three_survivor_cover (F : Nat → List (Vertex → Prop))
    (hd : DisjointParents F) (v : Vertex) :
    (Clear F 1 v ∧ Clear F 2 v) ∨
    (Clear F 0 v ∧ Clear F 2 v) ∨
    (Clear F 0 v ∧ Clear F 1 v) := by
  classical
  by_cases h0 : Occupies F 0 v
  · exact Or.inl ⟨fun h1 => distinct_parents_no_joint_owner F hd 0 1 (by decide) v ⟨h0,h1⟩,
      fun h2 => distinct_parents_no_joint_owner F hd 0 2 (by decide) v ⟨h0,h2⟩⟩
  · by_cases h1 : Occupies F 1 v
    · exact Or.inr (Or.inl ⟨h0,
        fun h2 => distinct_parents_no_joint_owner F hd 1 2 (by decide) v ⟨h1,h2⟩⟩)
    · exact Or.inr (Or.inr ⟨h0,h1⟩)

theorem chain_four_ownership_cover (F : Nat → List (Vertex → Prop))
    (hd : DisjointParents F) (v w : Vertex) :
    (Clear F 1 v ∧ Clear F 2 w) ∨
    (Clear F 1 v ∧ Clear F 1 w) ∨
    (Clear F 0 v ∧ Clear F 2 w) ∨
    (Clear F 0 v ∧ Clear F 1 w) := by
  classical
  have hv : Clear F 0 v ∨ Clear F 1 v := by
    by_cases h0 : Occupies F 0 v
    · exact Or.inr (fun h1 => distinct_parents_no_joint_owner F hd 0 1 (by decide) v ⟨h0,h1⟩)
    · exact Or.inl h0
  have hw : Clear F 1 w ∨ Clear F 2 w := by
    by_cases h1 : Occupies F 1 w
    · exact Or.inr (fun h2 => distinct_parents_no_joint_owner F hd 1 2 (by decide) w ⟨h1,h2⟩)
    · exact Or.inl h1
  rcases hv with h0 | h1 <;> rcases hw with hb | hc
  · exact Or.inr (Or.inr (Or.inr ⟨h0,hb⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨h0,hc⟩))
  · exact Or.inr (Or.inl ⟨h1,hb⟩)
  · exact Or.inl ⟨h1,hc⟩

/-- Paid diagonal: the binary clear of B OR two distinct-parent clears A,C.
The coincidence premise is obtained for every B-piece by the preceding
actual graph theorem, when the two joint leaf regions are nonempty. -/
theorem chain_two_paid_cover (F : Nat → List (Vertex → Prop))
    (hd : DisjointParents F) (v w : Vertex)
    (hcoinc : Occupies F 1 v ↔ Occupies F 1 w) :
    (Clear F 1 v ∧ Clear F 1 w) ∨ (Clear F 0 v ∧ Clear F 2 w) := by
  classical
  by_cases hb : Occupies F 1 v
  · exact Or.inr ⟨fun ha => distinct_parents_no_joint_owner F hd 0 1 (by decide) v ⟨ha,hb⟩,
      fun hc => distinct_parents_no_joint_owner F hd 1 2 (by decide) w ⟨hcoinc.1 hb,hc⟩⟩
  · exact Or.inl ⟨hb,fun hw => hb (hcoinc.2 hw)⟩

/-- Lowest common ancestor in unsuppressed original addresses. -/
def lca : Vertex → Vertex → Vertex
  | [], _ => []
  | _, [] => []
  | s :: a, t :: b => if s = t then s :: lca a b else []

theorem lca_on_path (a b : Vertex) : PathAt (lca a b) a b := by
  induction a generalizing b with
  | nil => exact PathAt.endpointL [] b
  | cons s a ih =>
    cases b with
    | nil => exact PathAt.endpointR (s :: a) []
    | cons t b =>
      by_cases e : s = t
      · subst t; simpa [lca] using PathAt.down s (ih b)
      · have h : PathAt [] (s :: a) (t :: b) := by
          cases s <;> cases t <;> simp_all
          · exact PathAt.fork a b
          · exact PathAt.fork' a b
        simpa [lca,e] using h

theorem lca_left_root (a b : Vertex) : PathAt (lca a b) a [] := by
  induction a generalizing b with
  | nil => exact PathAt.endpointL [] []
  | cons s a ih =>
    cases b with
    | nil => exact PathAt.endpointR (s :: a) []
    | cons t b =>
      by_cases e : s = t
      · subst t; simpa [lca] using PathAt.leftLeg s (ih b)
      · simpa [lca,e] using PathAt.endpointR (s :: a) []

theorem lca_right_root (a b : Vertex) : PathAt (lca a b) b [] := by
  induction a generalizing b with
  | nil => exact PathAt.endpointR b []
  | cons s a ih =>
    cases b with
    | nil => exact PathAt.endpointL [] []
    | cons t b =>
      by_cases e : s = t
      · subst t; simpa [lca] using PathAt.leftLeg s (ih b)
      · simpa [lca,e] using PathAt.endpointR (t :: b) []

/-- Explicit linear-address selector for the common point of three paths. -/
def median : Vertex → Vertex → Vertex → Vertex
  | [], b, c => lca b c
  | a, [], c => lca a c
  | a, b, [] => lca a b
  | s :: a, t :: b, u :: c =>
    if s = t then
      if t = u then s :: median a b c else s :: lca a b
    else if s = u then s :: lca a c else t :: lca b c

theorem median_on_three_paths (a b c : Vertex) :
    PathAt (median a b c) a b ∧ PathAt (median a b c) a c ∧
      PathAt (median a b c) b c := by
  induction a generalizing b c with
  | nil => exact ⟨path_sym (lca_left_root b c),path_sym (lca_right_root b c),lca_on_path b c⟩
  | cons s a ih =>
    cases b with
    | nil => exact ⟨lca_left_root (s :: a) c,lca_on_path (s :: a) c,
        path_sym (lca_right_root (s :: a) c)⟩
    | cons t b =>
      cases c with
      | nil => exact ⟨lca_on_path (s :: a) (t :: b),lca_left_root (s :: a) (t :: b),
          lca_right_root (s :: a) (t :: b)⟩
      | cons u c =>
        obtain ⟨hab,hac,hbc⟩ := ih b c
        cases s <;> cases t <;> cases u <;> simp only [median, Bool.false_eq_true,
          Bool.true_eq_false, ite_true, ite_false]
        · exact ⟨PathAt.down false hab,PathAt.down false hac,PathAt.down false hbc⟩
        · exact ⟨PathAt.down false (lca_on_path a b),
            PathAt.crossLeft false (lca_left_root a b),
            PathAt.crossLeft false (lca_right_root a b)⟩
        · exact ⟨PathAt.crossLeft false (lca_left_root a c),
            PathAt.down false (lca_on_path a c),
            PathAt.crossRight false (path_sym (lca_right_root a c))⟩
        · exact ⟨PathAt.crossRight true (path_sym (lca_left_root b c)),
            PathAt.crossRight true (path_sym (lca_right_root b c)),
            PathAt.down true (lca_on_path b c)⟩
        · exact ⟨PathAt.crossRight false (path_sym (lca_left_root b c)),
            PathAt.crossRight false (path_sym (lca_right_root b c)),
            PathAt.down false (lca_on_path b c)⟩
        · exact ⟨PathAt.crossLeft true (lca_left_root a c),
            PathAt.down true (lca_on_path a c),
            PathAt.crossRight true (path_sym (lca_right_root a c))⟩
        · exact ⟨PathAt.down true (lca_on_path a b),
            PathAt.crossLeft true (lca_left_root a b),
            PathAt.crossLeft true (lca_right_root a b)⟩
        · exact ⟨PathAt.down true hab,PathAt.down true hac,PathAt.down true hbc⟩

theorem region_root_when_up (v a : Vertex) (h : region v a = 2) : region v [] = 2 := by
  cases v with
  | nil => exact False.elim (region_root_not_up a h)
  | cons s v => rfl

/-- Components after deleting a vertex are convex for the actual unique path. -/
theorem region_path_closed {x a b : Vertex} (h : PathAt x a b)
    (v : Vertex) (heq : region v a = region v b) : region v x = region v a := by
  induction h generalizing v with
  | endpointL a b => rfl
  | endpointR a b => exact heq.symm
  | fork a b =>
    cases v with
    | nil => simp [region] at heq
    | cons s v => cases s <;> simp [region] at heq ⊢ <;> omega
  | fork' a b =>
    cases v with
    | nil => simp [region] at heq
    | cons s v => cases s <;> simp [region] at heq ⊢ <;> omega
  | @down s x a b h ih =>
    cases v with
    | nil => cases s <;> rfl
    | cons t v =>
      by_cases e : t = s
      · subst t; simpa [region] using ih v (by simpa [region] using heq)
      · simp [region,e]
  | @leftLeg s x a h ih =>
    cases v with
    | nil => cases s <;> simp [region] at heq
    | cons t v =>
      by_cases e : t = s
      · subst t
        have hh : region v a = 2 := by simpa [region] using heq
        have hr := region_root_when_up v a hh
        simpa [region] using ih v (hh.trans hr.symm)
      · simp [region,e]
  | @rightLeg s x b h ih =>
    cases v with
    | nil => cases s <;> simp [region] at heq
    | cons t v =>
      by_cases e : t = s
      · subst t
        have hh : region v b = 2 := by simpa [region] using heq.symm
        have hr := region_root_when_up v b hh
        simpa [region,hr] using ih v (hr.trans hh.symm)
      · simp [region,e]
  | @crossLeft s x a b h ih =>
    cases v with
    | nil => cases s <;> simp [region] at heq
    | cons t v =>
      by_cases e : t = s
      · subst t
        have hd : s ≠ !s := by cases s <;> decide
        have hh : region v a = 2 := by simpa [region,hd] using heq
        have hr := region_root_when_up v a hh
        simpa [region] using ih v (hh.trans hr.symm)
      · simp [region,e]
  | @crossRight s x a b h ih =>
    cases v with
    | nil => cases s <;> simp [region] at heq
    | cons t v =>
      by_cases e : t = s
      · subst t
        have hd : s ≠ !s := by cases s <;> decide
        have hh : region v b = 2 := by simpa [region,hd] using heq.symm
        have hr := region_root_when_up v b hh
        simpa [region,hd,hr,hh] using ih v (hr.trans hh.symm)
      · simpa [region,e] using heq.symm

def Convex (A : Vertex → Prop) : Prop :=
  ∀ v a b, A a → A b → PathAt v a b → A v

theorem hull_convex (S : Vertex → Prop) : Convex (Hull S) := by
  classical
  intro v a b ha hb hp
  by_cases hh : Hull S v
  · exact hh
  · have hlabel : ¬S v := by
      intro hs; exact hh ⟨v,v,hs,hs,PathAt.endpointL v v⟩
    have hmono := (avoids_iff_monochromatic S v hlabel).1 hh
    have hna : a ≠ v := by intro e; subst a; exact hh ha
    have hnb : b ≠ v := by intro e; subst b; exact hh hb
    rcases ha with ⟨a1,a2,ha1,ha2,hpa⟩
    rcases hb with ⟨b1,b2,hb1,hb2,hpb⟩
    have hea := region_path_closed hpa v (hmono a1 a2 ha1 ha2)
    have heb := region_path_closed hpb v (hmono b1 b2 hb1 hb2)
    exact False.elim (path_region_ne v a b hp hna hnb
      (hea.trans ((hmono a1 b1 ha1 hb1).trans heb.symm)))

/-- Vertex Helly for three arbitrary actual path-convex address subtrees. -/
theorem vertex_helly_three (A B C : Vertex → Prop)
    (hA : Convex A) (hB : Convex B) (hC : Convex C)
    (hAB : ∃ x, A x ∧ B x) (hBC : ∃ y, B y ∧ C y)
    (hAC : ∃ z, A z ∧ C z) : ∃ v, A v ∧ B v ∧ C v := by
  rcases hAB with ⟨x,hAx,hBx⟩
  rcases hBC with ⟨y,hBy,hCy⟩
  rcases hAC with ⟨z,hAz,hCz⟩
  obtain ⟨hxy,hxz,hyz⟩ := median_on_three_paths x y z
  exact ⟨median x y z,hA _ x z hAx hAz hxz,
    hB _ x y hBx hBy hxy,hC _ y z hCy hCz hyz⟩

/-- Actual minimal leaf hulls satisfy the clique consumer without a shared edge. -/
theorem leaf_hull_helly_three (S T U : Vertex → Prop)
    (hST : ∃ x, Hull S x ∧ Hull T x)
    (hTU : ∃ y, Hull T y ∧ Hull U y)
    (hSU : ∃ z, Hull S z ∧ Hull U z) :
    ∃ v, Hull S v ∧ Hull T v ∧ Hull U v :=
  vertex_helly_three (Hull S) (Hull T) (Hull U)
    (hull_convex S) (hull_convex T) (hull_convex U) hST hTU hSU

/-- Actual component equivalence after deleting a nonendpoint vertex. -/
theorem sameRegion_iff_path_avoids (v a b : Vertex) (ha : a ≠ v) (hb : b ≠ v) :
    SameRegion v a b ↔ ¬PathAt v a b := by
  constructor
  · intro heq hp; exact path_region_ne v a b hp ha hb heq
  · intro hn
    by_cases heq : region v a = region v b
    · exact heq
    · exact False.elim (hn (region_ne_path v a b heq))

/-- Double-removal joint colors are EXACT connected-component signatures:
the unique path avoids both deleted vertices iff both direction coordinates agree.
For selected leaves that path stays in the parent hull by hull_convex. -/
theorem jointRegion_iff_path_avoids (v w a b : Vertex)
    (hav : a ≠ v) (hbv : b ≠ v) (haw : a ≠ w) (hbw : b ≠ w) :
    jointRegion v w a = jointRegion v w b ↔ ¬PathAt v a b ∧ ¬PathAt w a b := by
  change (region v a,region w a) = (region v b,region w b) ↔ _
  rw [Prod.mk.injEq]
  exact and_congr (sameRegion_iff_path_avoids v a b hav hbv)
    (sameRegion_iff_path_avoids w a b haw hbw)
end VertexGeometry
