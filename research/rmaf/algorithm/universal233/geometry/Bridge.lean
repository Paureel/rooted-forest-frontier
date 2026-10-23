import Geometry
import RMAF
namespace VertexGeometry

def Join (S T : Vertex → Prop) : Vertex → Prop
  | [] => False
  | false :: a => S a
  | true :: a => T a

def Reach (S : Vertex → Prop) (v : Vertex) : Prop :=
  ∃ a, S a ∧ PathAt v a []

def Nonempty (S : Vertex → Prop) : Prop := ∃ a, S a

theorem reach_root (S : Vertex → Prop) : Reach S [] ↔ Nonempty S := by
  constructor
  · rintro ⟨a,ha,h⟩; exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩; exact ⟨a,ha,PathAt.endpointR a []⟩

theorem path_same_side (s : Bool) (v a b : Vertex) :
    PathAt (s :: v) (s :: a) (s :: b) ↔ PathAt v a b := by
  constructor
  · intro h
    by_cases ha : a = v
    · subst a; exact PathAt.endpointL v b
    · by_cases hb : b = v
      · subst b; exact PathAt.endpointR a v
      · exact region_ne_path v a b (by
          simpa [region] using path_region_ne _ _ _ h
            (by simpa using ha) (by simpa using hb))
  · exact PathAt.down s

theorem path_same_side_to_root (s : Bool) (v a : Vertex) :
    PathAt (s :: v) (s :: a) [] ↔ PathAt v a [] := by
  constructor
  · intro h
    by_cases ha : a = v
    · subst a; exact PathAt.endpointL v []
    · apply not_up_path_to_root
      simpa [region] using path_region_ne _ _ _ h (by simpa using ha) (by simp)
  · exact PathAt.leftLeg s

theorem path_cross_left (s : Bool) (v a b : Vertex) :
    PathAt (s :: v) (s :: a) ((!s) :: b) ↔ PathAt v a [] := by
  constructor
  · intro h
    by_cases ha : a = v
    · subst a; exact PathAt.endpointL v []
    · apply not_up_path_to_root
      have hd : s ≠ !s := by cases s <;> decide
      simpa [region,hd] using path_region_ne _ _ _ h (by simpa using ha)
        (by cases s <;> simp)
  · exact PathAt.crossLeft s

theorem path_other_to_root_impossible (s : Bool) (v a : Vertex) :
    ¬PathAt (s :: v) ((!s) :: a) [] := by
  intro h
  have hd : s ≠ !s := by cases s <;> decide
  have hn := path_region_ne _ _ _ h (by cases s <;> simp) (by simp)
  simp [region,hd] at hn

theorem path_other_same_impossible (s : Bool) (v a b : Vertex) :
    ¬PathAt (s :: v) ((!s) :: a) ((!s) :: b) := by
  intro h
  have hd : s ≠ !s := by cases s <;> decide
  have hn := path_region_ne _ _ _ h (by cases s <;> simp) (by cases s <;> simp)
  simp [region,hd] at hn

theorem path_root_same_impossible (s : Bool) (a b : Vertex) :
    ¬PathAt [] (s :: a) (s :: b) := by
  intro h
  have hn := path_region_ne _ _ _ h (by simp) (by simp)
  cases s <;> simp [region] at hn

theorem nonempty_join (S T : Vertex → Prop) :
    Nonempty (Join S T) ↔ Nonempty S ∨ Nonempty T := by
  constructor
  · rintro ⟨a,ha⟩
    cases a with
    | nil => exact False.elim ha
    | cons s a => cases s with
      | false => exact Or.inl ⟨a,ha⟩
      | true => exact Or.inr ⟨a,ha⟩
  · rintro (⟨a,ha⟩ | ⟨a,ha⟩)
    · exact ⟨false::a,ha⟩
    · exact ⟨true::a,ha⟩

theorem reach_join_side (S T : Vertex → Prop) (v : Vertex) :
    Reach (Join S T) (false :: v) ↔ Reach S v := by
  constructor
  · rintro ⟨a,ha,hp⟩
    cases a with
    | nil => exact False.elim ha
    | cons s a => cases s with
      | false => exact ⟨a,ha,(path_same_side_to_root false v a).1 hp⟩
      | true => exact False.elim (path_other_to_root_impossible false v a hp)
  · rintro ⟨a,ha,hp⟩
    exact ⟨false::a,ha,PathAt.leftLeg false hp⟩

theorem reach_join_right (S T : Vertex → Prop) (v : Vertex) :
    Reach (Join S T) (true :: v) ↔ Reach T v := by
  constructor
  · rintro ⟨a,ha,hp⟩
    cases a with
    | nil => exact False.elim ha
    | cons s a => cases s with
      | false => exact False.elim (path_other_to_root_impossible true v a hp)
      | true => exact ⟨a,ha,(path_same_side_to_root true v a).1 hp⟩
  · rintro ⟨a,ha,hp⟩
    exact ⟨true::a,ha,PathAt.leftLeg true hp⟩

theorem hull_join_root (S T : Vertex → Prop) :
    Hull (Join S T) [] ↔ Nonempty S ∧ Nonempty T := by
  constructor
  · rintro ⟨a,b,ha,hb,hp⟩
    cases a with
    | nil => exact False.elim ha
    | cons s a =>
      cases b with
      | nil => exact False.elim hb
      | cons t b =>
        cases s <;> cases t
        · exact False.elim (path_root_same_impossible false a b hp)
        · exact ⟨⟨a,ha⟩,⟨b,hb⟩⟩
        · exact ⟨⟨b,hb⟩,⟨a,ha⟩⟩
        · exact False.elim (path_root_same_impossible true a b hp)
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨false::a,true::b,ha,hb,PathAt.fork a b⟩

theorem hull_join_left (S T : Vertex → Prop) (v : Vertex) :
    Hull (Join S T) (false :: v) ↔ Hull S v ∨ (Reach S v ∧ Nonempty T) := by
  constructor
  · rintro ⟨a,b,ha,hb,hp⟩
    cases a with
    | nil => exact False.elim ha
    | cons s a =>
      cases b with
      | nil => exact False.elim hb
      | cons t b =>
        cases s <;> cases t
        · exact Or.inl ⟨a,b,ha,hb,(path_same_side false v a b).1 hp⟩
        · exact Or.inr ⟨⟨a,ha,(path_cross_left false v a b).1 hp⟩,⟨b,hb⟩⟩
        · exact Or.inr ⟨⟨b,hb,(path_cross_left false v b a).1 (path_sym hp)⟩,⟨a,ha⟩⟩
        · exact False.elim (path_other_same_impossible false v a b hp)
  · rintro (⟨a,b,ha,hb,hp⟩ | ⟨⟨a,ha,hp⟩,⟨b,hb⟩⟩)
    · exact ⟨false::a,false::b,ha,hb,PathAt.down false hp⟩
    · exact ⟨false::a,true::b,ha,hb,PathAt.crossLeft false hp⟩

theorem hull_join_right (S T : Vertex → Prop) (v : Vertex) :
    Hull (Join S T) (true :: v) ↔ Hull T v ∨ (Reach T v ∧ Nonempty S) := by
  constructor
  · rintro ⟨a,b,ha,hb,hp⟩
    cases a with
    | nil => exact False.elim ha
    | cons s a =>
      cases b with
      | nil => exact False.elim hb
      | cons t b =>
        cases s <;> cases t
        · exact False.elim (path_other_same_impossible true v a b hp)
        · exact Or.inr ⟨⟨b,hb,(path_cross_left true v b a).1 (path_sym hp)⟩,⟨a,ha⟩⟩
        · exact Or.inr ⟨⟨a,ha,(path_cross_left true v a b).1 hp⟩,⟨b,hb⟩⟩
        · exact Or.inl ⟨a,b,ha,hb,(path_same_side true v a b).1 hp⟩
  · rintro (⟨a,b,ha,hb,hp⟩ | ⟨⟨a,ha,hp⟩,⟨b,hb⟩⟩)
    · exact ⟨true::a,true::b,ha,hb,PathAt.down true hp⟩
    · exact ⟨true::a,false::b,ha,hb,PathAt.crossLeft true hp⟩

def selectedLeaves (D : List Nat) : RMAF.Tree → Vertex → Prop
  | .leaf x => fun a => a = [] ∧ x ∈ D
  | .node l r => Join (selectedLeaves D l) (selectedLeaves D r)


theorem path_identical (v a : Vertex) (h : PathAt v a a) : v = a := by
  by_cases heq : v = a
  · exact heq
  · exact False.elim (path_region_ne v a a h (Ne.symm heq) (Ne.symm heq) rfl)

theorem reach_singleton (D : List Nat) (x : Nat) (v : Vertex) :
    Reach (selectedLeaves D (.leaf x)) v ↔ v = [] ∧ x ∈ D := by
  constructor
  · rintro ⟨a,⟨rfl,hx⟩,hp⟩
    exact ⟨path_identical v [] hp,hx⟩
  · rintro ⟨rfl,hx⟩
    exact ⟨[],⟨rfl,hx⟩,PathAt.endpointL [] []⟩

theorem hull_singleton (D : List Nat) (x : Nat) (v : Vertex) :
    Hull (selectedLeaves D (.leaf x)) v ↔ v = [] ∧ x ∈ D := by
  constructor
  · rintro ⟨a,b,⟨rfl,hx⟩,⟨rfl,hy⟩,hp⟩
    exact ⟨path_identical v [] hp,hx⟩
  · rintro ⟨rfl,hx⟩
    exact ⟨[],[],⟨rfl,hx⟩,⟨rfl,hx⟩,PathAt.endpointL [] []⟩

theorem hull_subset_reach (S : Vertex → Prop) (v : Vertex) : Hull S v → Reach S v := by
  rintro ⟨a,b,ha,hb,hp⟩
  by_cases heq : region v a = 2
  · have hna : a ≠ v := by intro e; subst a; simp [region_self] at heq
    by_cases hbv : b = v
    · subst b; exact ⟨v,hb,PathAt.endpointL v []⟩
    · refine ⟨b,hb,not_up_path_to_root v b ?_⟩
      intro heqb
      exact path_region_ne v a b hp hna hbv (heq.trans heqb.symm)
  · exact ⟨a,ha,not_up_path_to_root v a heq⟩

theorem hull_or_reach (S : Vertex → Prop) (v : Vertex) :
    (Hull S v ∨ Reach S v) ↔ Reach S v :=
  ⟨fun h => h.elim (hull_subset_reach S v) id,Or.inr⟩

theorem rootedSpan_root (D : List Nat) (t : RMAF.Tree) :
    ([] ∈ RMAF.rootedSpan D t) ↔ RMAF.rootedSpan D t ≠ [] := by
  cases t with
  | leaf x => simp only [RMAF.rootedSpan]; split <;> simp
  | node l r => simp only [RMAF.rootedSpan]; split <;> simp

theorem isEmpty_true (L : List Vertex) : L.isEmpty = true ↔ L = [] := by
  cases L <;> simp

theorem rootspan_empty_from_correct (D : List Nat) (t : RMAF.Tree)
    (h : ([] ∈ RMAF.rootedSpan D t) ↔ Reach (selectedLeaves D t) []) :
    RMAF.rootedSpan D t = [] ↔ ¬Nonempty (selectedLeaves D t) := by
  have hh : RMAF.rootedSpan D t ≠ [] ↔ Nonempty (selectedLeaves D t) :=
    (rootedSpan_root D t).symm.trans (h.trans (reach_root _))
  constructor
  · intro he hn; exact hh.2 hn he
  · intro hn
    by_cases he : RMAF.rootedSpan D t = []
    · exact he
    · exact False.elim (hn (hh.1 he))

theorem rootedSpan_correct (D : List Nat) (t : RMAF.Tree) (v : Vertex) :
    v ∈ RMAF.rootedSpan D t ↔ Reach (selectedLeaves D t) v := by
  classical
  induction t generalizing v with
  | leaf x =>
    rw [reach_singleton]
    simp only [RMAF.rootedSpan]
    split <;> simp_all
  | node l r ihl ihr =>
    have hL := rootspan_empty_from_correct D l (ihl [])
    have hR := rootspan_empty_from_correct D r (ihr [])
    cases eL : (RMAF.rootedSpan D l).isEmpty <;>
      cases eR : (RMAF.rootedSpan D r).isEmpty
    all_goals
      have hnl : Nonempty (selectedLeaves D l) ↔ (RMAF.rootedSpan D l).isEmpty = false := by
        simp [Bool.eq_false_iff, ne_eq, hL]
      have hnr : Nonempty (selectedLeaves D r) ↔ (RMAF.rootedSpan D r).isEmpty = false := by
        simp [Bool.eq_false_iff, ne_eq, hR]
      cases v with
      | nil =>
        simp [RMAF.rootedSpan,eL,eR,selectedLeaves,reach_root,nonempty_join,hnl,hnr]
      | cons s v =>
        cases s with
        | false =>
          simp only [selectedLeaves,reach_join_side]
          rw [← ihl v]
          simp [RMAF.rootedSpan,eL,eR,RMAF.prependSide]
          all_goals
            have : RMAF.rootedSpan D l = [] := (isEmpty_true _).1 eL
            simp [this]
        | true =>
          simp only [selectedLeaves,reach_join_right]
          rw [← ihr v]
          simp [RMAF.rootedSpan,eL,eR,RMAF.prependSide]
          all_goals
            have : RMAF.rootedSpan D r = [] := (isEmpty_true _).1 eR
            simp [this]

/-- Exact source-bound executable bridge: the checker collision list is the
actual minimal leaf-address graph hull, including singleton and empty cases. -/
theorem minimalVertices_correct (D : List Nat) (t : RMAF.Tree) (v : Vertex) :
    v ∈ RMAF.minimalVertices D t ↔ Hull (selectedLeaves D t) v := by
  classical
  induction t generalizing v with
  | leaf x =>
    rw [hull_singleton]
    simp only [RMAF.minimalVertices]
    split <;> simp_all
  | node l r ihl ihr =>
    have hL := rootspan_empty_from_correct D l (rootedSpan_correct D l [])
    have hR := rootspan_empty_from_correct D r (rootedSpan_correct D r [])
    have hnl : Nonempty (selectedLeaves D l) ↔ (RMAF.rootedSpan D l).isEmpty = false := by
      simp [Bool.eq_false_iff, ne_eq, hL]
    have hnr : Nonempty (selectedLeaves D r) ↔ (RMAF.rootedSpan D r).isEmpty = false := by
      simp [Bool.eq_false_iff, ne_eq, hR]
    cases eL : (RMAF.rootedSpan D l).isEmpty <;>
      cases eR : (RMAF.rootedSpan D r).isEmpty
    all_goals
      try have ll : RMAF.rootedSpan D l = [] := (isEmpty_true _).1 eL
    all_goals
      try have rr : RMAF.rootedSpan D r = [] := (isEmpty_true _).1 eR
    all_goals
      cases v with
      | nil =>
        simp [RMAF.minimalVertices,eL,eR,selectedLeaves,hull_join_root,hnl,hnr,RMAF.prependSide]
      | cons s v =>
        cases s with
        | false =>
          simp only [selectedLeaves,hull_join_left]
          simp [hnr,← rootedSpan_correct,← ihl,
            RMAF.minimalVertices,eL,eR,RMAF.prependSide]
          all_goals
            simp_all
          all_goals
            intro hh
            have hm := (rootedSpan_correct D l v).2 (hull_subset_reach _ v hh)
            first | exact hm | simp_all
        | true =>
          simp only [selectedLeaves,hull_join_right]
          simp [hnl,← rootedSpan_correct,← ihr,
            RMAF.minimalVertices,eL,eR,RMAF.prependSide]
          all_goals
            simp_all
          all_goals
            intro hh
            have hm := (rootedSpan_correct D r v).2 (hull_subset_reach _ v hh)
            first | exact hm | simp_all

theorem selected_leaf_reach_implies_self (D E : List Nat) (t : RMAF.Tree) (v : Vertex)
    (hd : selectedLeaves D t v) (he : Reach (selectedLeaves E t) v) :
    selectedLeaves E t v := by
  induction t generalizing v with
  | leaf x => exact (reach_singleton E x v).1 he
  | node l r ihl ihr =>
    cases v with
    | nil => exact False.elim hd
    | cons s v =>
      cases s with
      | false => exact ihl v hd ((reach_join_side _ _ v).1 he)
      | true => exact ihr v hd ((reach_join_right _ _ v).1 he)

theorem selected_leaves_disjoint (D E : List Nat) (t : RMAF.Tree)
    (hDE : ∀ x, x ∈ D → x ∈ E → False) :
    ∀ v, ¬(selectedLeaves D t v ∧ selectedLeaves E t v) := by
  induction t with
  | leaf x =>
    intro v ⟨⟨hv,hd⟩,⟨hv',he⟩⟩
    exact hDE x hd he
  | node l r ihl ihr =>
    intro v h
    cases v with
    | nil => exact h.1
    | cons s v => cases s with
      | false => exact ihl v h
      | true => exact ihr v h

/-- Actual parent overlap cannot be a selected label in either parent. This
extracts the nonterminal hypothesis from disjoint original parent labels. -/
theorem disjoint_parent_overlap_nonlabel (D E : List Nat) (t : RMAF.Tree) (v : Vertex)
    (hDE : ∀ x, x ∈ D → x ∈ E → False)
    (hd : v ∈ RMAF.minimalVertices D t) (he : v ∈ RMAF.minimalVertices E t) :
    ¬selectedLeaves D t v ∧ ¬selectedLeaves E t v := by
  have hd' := (minimalVertices_correct D t v).1 hd
  have he' := (minimalVertices_correct E t v).1 he
  constructor
  · intro hs
    have hsE := selected_leaf_reach_implies_self D E t v hs (hull_subset_reach _ v he')
    exact selected_leaves_disjoint D E t hDE v ⟨hs,hsE⟩
  · intro hs
    have hsD := selected_leaf_reach_implies_self E D t v hs (hull_subset_reach _ v hd')
    exact selected_leaves_disjoint D E t hDE v ⟨hsD,hs⟩

theorem executable_vertex_helly (t : RMAF.Tree) (A B C : List Nat)
    (hAB : ∃ x, x ∈ RMAF.minimalVertices A t ∧ x ∈ RMAF.minimalVertices B t)
    (hBC : ∃ x, x ∈ RMAF.minimalVertices B t ∧ x ∈ RMAF.minimalVertices C t)
    (hAC : ∃ x, x ∈ RMAF.minimalVertices A t ∧ x ∈ RMAF.minimalVertices C t) :
    ∃ v, v ∈ RMAF.minimalVertices A t ∧ v ∈ RMAF.minimalVertices B t ∧
      v ∈ RMAF.minimalVertices C t := by
  simp only [minimalVertices_correct] at hAB hBC hAC ⊢
  exact leaf_hull_helly_three _ _ _ hAB hBC hAC

theorem executable_avoids_regions (t : RMAF.Tree) (D : List Nat) (v : Vertex)
    (hn : ¬selectedLeaves D t v) :
    (v ∉ RMAF.minimalVertices D t) ↔
      ∀ a b, selectedLeaves D t a → selectedLeaves D t b → SameRegion v a b := by
  simpa only [minimalVertices_correct] using avoids_iff_monochromatic (selectedLeaves D t) v hn

theorem selected_leaves_mono (D E : List Nat) (t : RMAF.Tree)
    (h : ∀ x, x ∈ D → x ∈ E) : ∀ v, selectedLeaves D t v → selectedLeaves E t v := by
  induction t with
  | leaf x => intro v hv; exact ⟨hv.1,h x hv.2⟩
  | node l r ihl ihr =>
    intro v hv
    cases v with
    | nil => exact False.elim hv
    | cons s v => cases s with
      | false => exact ihl v hv
      | true => exact ihr v hv

theorem executable_two_region_coincidence (t : RMAF.Tree) (D P : List Nat) (v w : Vertex)
    (hnv : ¬selectedLeaves D t v) (hnw : ¬selectedLeaves D t w)
    (hv : v ∈ RMAF.minimalVertices D t) (hw : w ∈ RMAF.minimalVertices D t)
    (hr : TwoJointRegions (selectedLeaves D t) v w)
    (hsub : ∀ x, x ∈ P → x ∈ D) :
    v ∈ RMAF.minimalVertices P t ↔ w ∈ RMAF.minimalVertices P t := by
  simp only [minimalVertices_correct] at hv hw ⊢
  exact two_region_coincident_occupancy _ _ v w hnv hnw hv hw hr
    (selected_leaves_mono P D t hsub)

def leafList (D : List Nat) : RMAF.Tree → List Vertex
  | .leaf x => if D.contains x then [[]] else []
  | .node l r => RMAF.prependSide false (leafList D l) ++
      RMAF.prependSide true (leafList D r)

theorem leafList_correct (D : List Nat) (t : RMAF.Tree) (v : Vertex) :
    v ∈ leafList D t ↔ selectedLeaves D t v := by
  induction t generalizing v with
  | leaf x => simp only [leafList]; split <;> simp_all [selectedLeaves]
  | node l r ihl ihr =>
    cases v with
    | nil => simp [leafList,RMAF.prependSide,selectedLeaves,Join]
    | cons s v => cases s <;> simp [leafList,RMAF.prependSide,selectedLeaves,Join,ihl,ihr]

/-- Only nonempty LEAF regions count. Leafless vertices and paths create no color. -/
def regions (D : List Nat) (t : RMAF.Tree) (v : Vertex) : List Nat :=
  [0,1,2].filter (fun c => (leafList D t).any (fun a => region v a == c))

theorem regionList_mem (D : List Nat) (t : RMAF.Tree) (v : Vertex) (c : Nat) :
    c ∈ regions D t v ↔ c < 3 ∧ ∃ a, selectedLeaves D t a ∧ region v a = c := by
  simp only [regions,List.mem_filter,List.mem_cons,List.not_mem_nil,or_false,
    List.any_eq_true,beq_iff_eq,leafList_correct]
  constructor
  · rintro ⟨hc,ha⟩; exact ⟨by omega,ha⟩
  · rintro ⟨hc,ha⟩; exact ⟨by omega,ha⟩

/-- The number of nonempty leaf regions at every actual nonlabel overlap is
exactly two or three. The proof handles all eight possible region-flag patterns. -/
theorem executable_region_count_two_or_three (D : List Nat) (t : RMAF.Tree) (v : Vertex)
    (hn : ¬selectedLeaves D t v) (hv : v ∈ RMAF.minimalVertices D t) :
    (regions D t v).length = 2 ∨ (regions D t v).length = 3 := by
  obtain ⟨a,b,ha,hb,hca,hcb,hab⟩ := occupied_nonlabel_two_directions _ v hn
    ((minimalVertices_correct D t v).1 hv)
  have ham : region v a ∈ regions D t v := (regionList_mem D t v _).2 ⟨hca,⟨a,ha,rfl⟩⟩
  have hbm : region v b ∈ regions D t v := (regionList_mem D t v _).2 ⟨hcb,⟨b,hb,rfl⟩⟩
  unfold regions at ham hbm ⊢
  cases h0 : (leafList D t).any (fun a => region v a == 0) <;>
    cases h1 : (leafList D t).any (fun a => region v a == 1) <;>
    cases h2 : (leafList D t).any (fun a => region v a == 2) <;>
    simp [h0,h1,h2] at ham hbm ⊢ <;> omega

theorem executable_disjointVertices (t : RMAF.Tree) (D E : List Nat) :
    RMAF.disjointVertices (RMAF.minimalVertices D t) (RMAF.minimalVertices E t) = true ↔
    ∀ v, ¬(Hull (selectedLeaves D t) v ∧ Hull (selectedLeaves E t) v) := by
  simp only [RMAF.disjointVertices,List.all_eq_true]
  simp only [Bool.not_eq_true',Bool.eq_false_iff]
  simp only [ne_eq,List.contains_iff_mem,minimalVertices_correct]
  constructor
  · intro h v ⟨hd,he⟩; exact h v hd he
  · intro h v hd he; exact h v ⟨hd,he⟩

theorem executable_pairwiseEmbeddings (t : RMAF.Tree) (bs : List (List Nat)) :
    RMAF.pairwiseEmbeddings t bs = true ↔
    bs.Pairwise (fun D E => ∀ v,
      ¬(Hull (selectedLeaves D t) v ∧ Hull (selectedLeaves E t) v)) := by
  induction bs with
  | nil => simp [RMAF.pairwiseEmbeddings]
  | cons b bs ih =>
    simp only [RMAF.pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true,
      executable_disjointVertices,ih,List.pairwise_cons]

/-- Executable colors of nonempty components after deleting BOTH targets.
The two-coordinate signature excludes every leafless middle component. -/
def jointColors (D : List Nat) (t : RMAF.Tree) (v w : Vertex) : List (Nat × Nat) :=
  ((leafList D t).map (jointRegion v w)).eraseDups

theorem jointColors_mem (D : List Nat) (t : RMAF.Tree) (v w : Vertex) (c : Nat × Nat) :
    c ∈ jointColors D t v w ↔ ∃ a, selectedLeaves D t a ∧ jointRegion v w a = c := by
  simp [jointColors,List.mem_map,leafList_correct]

theorem two_members_length {α : Type} (L : List α) (a b : α)
    (ha : a ∈ L) (hb : b ∈ L) (hne : a ≠ b) : 2 ≤ L.length := by
  cases L with
  | nil => simp at ha
  | cons x xs =>
    cases xs with
    | nil => simp_all
    | cons y ys => simp

theorem jointColors_at_least_two (D : List Nat) (t : RMAF.Tree) (v w : Vertex)
    (hnv : ¬selectedLeaves D t v) (hv : v ∈ RMAF.minimalVertices D t) :
    2 ≤ (jointColors D t v w).length := by
  obtain ⟨a,b,ha,hb,hca,hcb,hab⟩ := occupied_nonlabel_two_directions _ v hnv
    ((minimalVertices_correct D t v).1 hv)
  apply two_members_length _ (jointRegion v w a) (jointRegion v w b)
  · exact (jointColors_mem D t v w _).2 ⟨a,ha,rfl⟩
  · exact (jointColors_mem D t v w _).2 ⟨b,hb,rfl⟩
  · intro e; exact hab (congrArg Prod.fst e)

theorem twoJointRegions_of_count_two (D : List Nat) (t : RMAF.Tree) (v w : Vertex)
    (hnv : ¬selectedLeaves D t v) (hnw : ¬selectedLeaves D t w)
    (hv : v ∈ RMAF.minimalVertices D t) (hw : w ∈ RMAF.minimalVertices D t)
    (hc : (jointColors D t v w).length = 2) : TwoJointRegions (selectedLeaves D t) v w := by
  cases he : jointColors D t v w with
  | nil => simp [he] at hc
  | cons p ps =>
    cases ps with
    | nil => simp [he] at hc
    | cons q qs =>
      have hqs : qs = [] := by cases qs <;> simp_all
      subst qs
      obtain ⟨a,ha,hpa⟩ := (jointColors_mem D t v w p).1 (by simp [he])
      obtain ⟨b,hb,hpb⟩ := (jointColors_mem D t v w q).1 (by simp [he])
      have hcover : ∀ x, selectedLeaves D t x → jointRegion v w x = jointRegion v w a ∨
          jointRegion v w x = jointRegion v w b := by
        intro x hx
        have hxm := (jointColors_mem D t v w (jointRegion v w x)).2 ⟨x,hx,rfl⟩
        simpa [he,hpa,hpb] using hxm
      have hsep := (two_joint_coordinate_separation _ v w a b hnv hnw
        ((minimalVertices_correct D t v).1 hv) ((minimalVertices_correct D t w).1 hw) hcover).1
      exact ⟨a,b,ha,hb,(fun e => hsep (congrArg Prod.fst e)),hcover⟩

/-- The executable double-removal branch is exhaustive: r≥3 or paid r=2;
r=0 and r=1 are excluded from actual occupied nonlabel span geometry. -/
theorem executable_joint_region_dichotomy (D : List Nat) (t : RMAF.Tree) (v w : Vertex)
    (hnv : ¬selectedLeaves D t v) (hv : v ∈ RMAF.minimalVertices D t) :
    (jointColors D t v w).length = 2 ∨ 3 ≤ (jointColors D t v w).length := by
  have h := jointColors_at_least_two D t v w hnv hv
  omega

theorem singleton_selected_exists (t : RMAF.Tree) (x : Nat) :
    (∃ a, selectedLeaves [x] t a) ↔ x ∈ RMAF.leaves t := by
  induction t with
  | leaf y => simp [selectedLeaves,RMAF.leaves,eq_comm]
  | node l r ihl ihr =>
    change Nonempty (Join (selectedLeaves [x] l) (selectedLeaves [x] r)) ↔
      x ∈ RMAF.leaves l ++ RMAF.leaves r
    rw [nonempty_join]
    simpa only [Nonempty,List.mem_append] using or_congr ihl ihr

theorem singleton_selected_address_unique (t : RMAF.Tree) (x : Nat)
    (hn : (RMAF.leaves t).Nodup) (a b : Vertex)
    (ha : selectedLeaves [x] t a) (hb : selectedLeaves [x] t b) : a = b := by
  induction t generalizing a b with
  | leaf y => exact ha.1.trans hb.1.symm
  | node l r ihl ihr =>
    obtain ⟨hnl,hnr,hnlr⟩ := List.nodup_append.1 hn
    cases a with
    | nil => exact False.elim ha
    | cons s a =>
      cases b with
      | nil => exact False.elim hb
      | cons u b =>
        cases s <;> cases u
        · exact congrArg (false :: ·) (ihl hnl a b ha hb)
        · exact False.elim (hnlr x ((singleton_selected_exists l x).1 ⟨a,ha⟩)
            x ((singleton_selected_exists r x).1 ⟨b,hb⟩) rfl)
        · exact False.elim (hnlr x ((singleton_selected_exists l x).1 ⟨b,hb⟩)
            x ((singleton_selected_exists r x).1 ⟨a,ha⟩) rfl)
        · exact congrArg (true :: ·) (ihr hnr a b ha hb)

/-- A concrete original-label coloring: locate the unique unsuppressed target
leaf, then color by its deletion region. Only proper labels are consumed. -/
def colorLabel (t : RMAF.Tree) (v : Vertex) (x : Nat) : Nat :=
  region v ((leafList [x] t).headD [])

theorem colorLabel_at_address (t : RMAF.Tree) (v : Vertex) (x : Nat)
    (hn : (RMAF.leaves t).Nodup) (a : Vertex) (ha : selectedLeaves [x] t a) :
    colorLabel t v x = region v a := by
  have hm := (leafList_correct [x] t a).2 ha
  unfold colorLabel
  cases he : leafList [x] t with
  | nil => simp [he] at hm
  | cons b bs =>
    have hb := (leafList_correct [x] t b).1 (by simp [he])
    have eqba := singleton_selected_address_unique t x hn b a hb ha
    simp [eqba]

theorem selected_decompose_label (D : List Nat) (t : RMAF.Tree) (a : Vertex) :
    selectedLeaves D t a ↔ ∃ x, x ∈ D ∧ selectedLeaves [x] t a := by
  induction t generalizing a with
  | leaf y =>
    constructor
    · intro h; exact ⟨y,h.2,h.1,by simp⟩
    · rintro ⟨x,hx,he,hyx⟩
      have hy : y = x := by simpa using hyx
      exact ⟨he,by simpa [hy] using hx⟩
  | node l r ihl ihr =>
    cases a with
    | nil => simp [selectedLeaves,Join]
    | cons s a => cases s with
      | false => simpa only [selectedLeaves,Join] using ihl a
      | true => simpa only [selectedLeaves,Join] using ihr a

def LabelMonochromatic (color : Nat → Nat) (P : List Nat) : Prop :=
  ∀ x y, x ∈ P → y ∈ P → color x = color y

/-- Exact ORIGINAL-LABEL core coloring interface. Restriction suppression has
no role: every label is colored at its full-input unsuppressed leaf address. -/
theorem original_label_avoids_iff (t : RMAF.Tree) (D : List Nat) (v : Vertex)
    (hn : (RMAF.leaves t).Nodup) (hlabels : ∀ x, x ∈ D → x ∈ RMAF.leaves t)
    (hno : ¬selectedLeaves D t v) :
    (v ∉ RMAF.minimalVertices D t) ↔ LabelMonochromatic (colorLabel t v) D := by
  rw [executable_avoids_regions t D v hno]
  constructor
  · intro hmono x y hx hy
    obtain ⟨a,ha⟩ := (singleton_selected_exists t x).2 (hlabels x hx)
    obtain ⟨b,hb⟩ := (singleton_selected_exists t y).2 (hlabels y hy)
    rw [colorLabel_at_address t v x hn a ha,colorLabel_at_address t v y hn b hb]
    exact hmono a b ((selected_decompose_label D t a).2 ⟨x,hx,ha⟩)
      ((selected_decompose_label D t b).2 ⟨y,hy,hb⟩)
  · intro hmono a b ha hb
    obtain ⟨x,hx,hxa⟩ := (selected_decompose_label D t a).1 ha
    obtain ⟨y,hy,hyb⟩ := (selected_decompose_label D t b).1 hb
    have heq := hmono x y hx hy
    change region v a = region v b
    simpa only [colorLabel_at_address t v x hn a hxa,
      colorLabel_at_address t v y hn b hyb] using heq

/-- No artificial stem/rho: an occupied original input root has exactly its
two child leaf regions, never a third upward region. -/
theorem executable_root_region_count_two (D : List Nat) (t : RMAF.Tree)
    (hn : ¬selectedLeaves D t []) (hv : [] ∈ RMAF.minimalVertices D t) :
    (regions D t []).length = 2 := by
  have hc := executable_region_count_two_or_three D t [] hn hv
  have h2 : (leafList D t).any (fun a => region [] a == 2) = false := by
    apply Bool.eq_false_iff.2
    intro hh
    obtain ⟨a,ha,he⟩ := List.any_eq_true.1 hh
    exact region_root_not_up a (beq_iff_eq.1 he)
  unfold regions at hc ⊢
  cases h0 : (leafList D t).any (fun a => region [] a == 0) <;>
    cases h1 : (leafList D t).any (fun a => region [] a == 1) <;>
    simp [h0,h1,h2] at hc ⊢

/-- In a chain with disjoint endpoint target spans the chosen overlap vertices
are distinct; equality would put that vertex in both endpoint spans. -/
theorem executable_chain_targets_distinct (t : RMAF.Tree) (A C : List Nat) (v w : Vertex)
    (hAC : RMAF.disjointVertices (RMAF.minimalVertices A t) (RMAF.minimalVertices C t) = true)
    (hv : v ∈ RMAF.minimalVertices A t) (hw : w ∈ RMAF.minimalVertices C t) : v ≠ w := by
  intro e
  subst w
  exact (executable_disjointVertices t A C).1 hAC v
    ⟨(minimalVertices_correct A t v).1 hv,(minimalVertices_correct C t v).1 hw⟩

/-- Concrete selector: at most one predicate evaluation per A-span vertex. -/
def findCommon (A B C : List Vertex) : Option Vertex :=
  match A with
  | [] => none
  | v :: vs => if B.contains v && C.contains v then some v else findCommon vs B C

def commonPredicateCalls (A B C : List Vertex) : Nat :=
  match A with
  | [] => 0
  | v :: vs => if B.contains v && C.contains v then 1 else 1 + commonPredicateCalls vs B C

theorem commonPredicateCalls_bound (A B C : List Vertex) : commonPredicateCalls A B C ≤ A.length := by
  induction A with
  | nil => simp [commonPredicateCalls]
  | cons v vs ih => simp only [commonPredicateCalls]; split <;> simp_all; omega

theorem findCommon_sound (A B C : List Vertex) (v : Vertex) (h : findCommon A B C = some v) :
    v ∈ A ∧ v ∈ B ∧ v ∈ C := by
  induction A with
  | nil => simp [findCommon] at h
  | cons x xs ih =>
    simp only [findCommon] at h
    split at h
    next hh =>
      have he : x = v := Option.some.inj h
      subst x
      have hbc : B.contains v = true ∧ C.contains v = true := by
        simpa only [Bool.and_eq_true] using hh
      exact ⟨by simp,List.contains_iff_mem.1 hbc.1,List.contains_iff_mem.1 hbc.2⟩
    next hh =>
      obtain ⟨ha,hb,hc⟩ := ih h
      exact ⟨by simp [ha],hb,hc⟩

theorem findCommon_complete (A B C : List Vertex)
    (h : ∃ v, v ∈ A ∧ v ∈ B ∧ v ∈ C) : ∃ v, findCommon A B C = some v := by
  induction A with
  | nil => simp at h
  | cons x xs ih =>
    simp only [findCommon]
    split
    next hh => exact ⟨x,rfl⟩
    next hh =>
      apply ih
      rcases h with ⟨v,hv,hB,hC⟩
      simp only [List.mem_cons] at hv
      rcases hv with hv | hv
      · subst v
        exact False.elim (hh (by simp [hB,hC]))
      · exact ⟨v,hv,hB,hC⟩

/-- The executable clique macro has a concrete terminating selector on its
actual span lists, whose successful result lies in all three target spans. -/
theorem executable_clique_selector (t : RMAF.Tree) (A B C : List Nat)
    (hAB : ∃ x, x ∈ RMAF.minimalVertices A t ∧ x ∈ RMAF.minimalVertices B t)
    (hBC : ∃ x, x ∈ RMAF.minimalVertices B t ∧ x ∈ RMAF.minimalVertices C t)
    (hAC : ∃ x, x ∈ RMAF.minimalVertices A t ∧ x ∈ RMAF.minimalVertices C t) :
    ∃ v, findCommon (RMAF.minimalVertices A t) (RMAF.minimalVertices B t)
      (RMAF.minimalVertices C t) = some v ∧
      v ∈ RMAF.minimalVertices A t ∧ v ∈ RMAF.minimalVertices B t ∧
        v ∈ RMAF.minimalVertices C t := by
  obtain ⟨v,hv⟩ := findCommon_complete _ _ _ (executable_vertex_helly t A B C hAB hBC hAC)
  exact ⟨v,hv,findCommon_sound _ _ _ v hv⟩
end VertexGeometry
