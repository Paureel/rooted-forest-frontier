import Restriction
import Bridge
namespace BinaryExchange
open RMAF VertexGeometry

/-- True-colored selected leaves are empty or one rooted cluster. This is
proved from tree constructors, never supplied as an exchange premise. -/
inductive Cluster (p : Nat → Prop) (q : Nat → Bool) : Tree → Prop
  | allTrue {t} : (∀ x, x ∈ leaves t → p x → q x = true) → Cluster p q t
  | allFalse {t} : (∀ x, x ∈ leaves t → p x → q x = false) → Cluster p q t
  | left {l r} : Cluster p q l →
      (∀ x, x ∈ leaves r → p x → q x = false) → Cluster p q (.node l r)
  | right {l r} : (∀ x, x ∈ leaves l → p x → q x = false) →
      Cluster p q r → Cluster p q (.node l r)

def yes (C : List Nat) (q : Nat → Bool) := C.filter q
def no (C : List Nat) (q : Nat → Bool) := C.filter (fun x => !q x)

theorem cluster_iso {p : Nat → Prop} {q : Nat → Bool} {s t : Tree}
    (h : RootedIso s t) (hc : Cluster p q s) : Cluster p q t := by
  induction h with
  | leaf x => exact hc
  | @straight a b c d h1 h2 ih1 ih2 =>
    cases hc with
    | allTrue h => exact .allTrue (by intro x hx hp; apply h x _ hp; simpa only [leaves,List.mem_append,iso_leaves h1,iso_leaves h2] using hx)
    | allFalse h => exact .allFalse (by intro x hx hp; apply h x _ hp; simpa only [leaves,List.mem_append,iso_leaves h1,iso_leaves h2] using hx)
    | left hc hn => exact .left (ih1 hc) (by intro x hx hp; exact hn x ((iso_leaves h2 x).2 hx) hp)
    | right hn hc => exact .right (by intro x hx hp; exact hn x ((iso_leaves h1 x).2 hx) hp) (ih2 hc)
  | @swapped a b c d h1 h2 ih1 ih2 =>
    cases hc with
    | allTrue h => exact .allTrue (by intro x hx hp; apply h x _ hp; simp only [leaves,List.mem_append,iso_leaves h1,iso_leaves h2]; simpa only [leaves,List.mem_append,or_comm] using hx)
    | allFalse h => exact .allFalse (by intro x hx hp; apply h x _ hp; simp only [leaves,List.mem_append,iso_leaves h1,iso_leaves h2]; simpa only [leaves,List.mem_append,or_comm] using hx)
    | left hc hn => exact .right (by intro x hx hp; exact hn x ((iso_leaves h2 x).2 hx) hp) (ih1 hc)
    | right hn hc => exact .left (ih2 hc) (by intro x hx hp; exact hn x ((iso_leaves h1 x).2 hx) hp)

theorem cluster_restrict {p : Nat → Prop} {q : Nat → Bool} {t u : Tree}
    (hc : Cluster p q t) (C : List Nat) (hC : ∀ x, x ∈ C → p x)
    (hu : restrict C t = some u) : Cluster (fun _ => True) q u := by
  induction hc generalizing u with
  | allTrue h => exact .allTrue (by intro x hx hp; obtain ⟨ht,hc⟩ := (restrict_mem C _ u hu x).1 hx; exact h x ht (hC x hc))
  | allFalse h => exact .allFalse (by intro x hx hp; obtain ⟨ht,hc⟩ := (restrict_mem C _ u hu x).1 hx; exact h x ht (hC x hc))
  | @left l r hc hn ih =>
    cases el : restrict C l <;> cases er : restrict C r
    · simp [restrict,el,er] at hu
    · have eu : u = _ := Option.some.inj (by simpa [restrict,el,er] using hu.symm)
      subst u
      exact .allFalse (by intro x hx hp; obtain ⟨ht,hc⟩ := (restrict_mem C r _ er x).1 hx; exact hn x ht (hC x hc))
    · have eu : u = _ := Option.some.inj (by simpa [restrict,el,er] using hu.symm)
      subst u; exact ih el
    · have eu : u = _ := Option.some.inj (by simpa [restrict,el,er] using hu.symm)
      subst u
      exact .left (ih el) (by intro x hx hp; obtain ⟨ht,hc⟩ := (restrict_mem C r _ er x).1 hx; exact hn x ht (hC x hc))
  | @right l r hn hc ih =>
    cases el : restrict C l <;> cases er : restrict C r
    · simp [restrict,el,er] at hu
    · have eu : u = _ := Option.some.inj (by simpa [restrict,el,er] using hu.symm)
      subst u; exact ih er
    · have eu : u = _ := Option.some.inj (by simpa [restrict,el,er] using hu.symm)
      subst u
      exact .allFalse (by intro x hx hp; obtain ⟨ht,hc⟩ := (restrict_mem C l _ el x).1 hx; exact hn x ht (hC x hc))
    · have eu : u = _ := Option.some.inj (by simpa [restrict,el,er] using hu.symm)
      subst u
      exact .right (by intro x hx hp; obtain ⟨ht,hc⟩ := (restrict_mem C l _ el x).1 hx; exact hn x ht (hC x hc)) (ih er)

theorem cluster_lift (C : List Nat) (q : Nat → Bool) (t u : Tree)
    (hu : restrict C t = some u) (hc : Cluster (fun _ => True) q u) :
    Cluster (fun x => x ∈ C) q t := by
  induction t generalizing u with
  | leaf x =>
    by_cases hx : x ∈ C
    · have eu : u = .leaf x := by simpa [restrict,hx] using hu.symm
      subst u
      cases hc with
      | allTrue h => exact .allTrue (fun y hy hp => h y hy trivial)
      | allFalse h => exact .allFalse (fun y hy hp => h y hy trivial)
    · simp [restrict,hx] at hu
  | node l r ihl ihr =>
    cases el : restrict C l <;> cases er : restrict C r
    · simp [restrict,el,er] at hu
    · have eu : u = _ := Option.some.inj (by simpa [restrict,el,er] using hu.symm)
      subst u
      exact .right (by intro x hx hp; exact False.elim ((restrict_none_iff C l).1 el x hx hp)) (ihr _ er hc)
    · have eu : u = _ := Option.some.inj (by simpa [restrict,el,er] using hu.symm)
      subst u
      exact .left (ihl _ el hc) (by intro x hx hp; exact False.elim ((restrict_none_iff C r).1 er x hx hp))
    · have eu : u = _ := Option.some.inj (by simpa [restrict,el,er] using hu.symm)
      subst u
      cases hc with
      | allTrue h =>
        exact .allTrue (by intro x hx hp; apply h x _ trivial; exact (restrict_mem C (.node l r) _ hu x).2 ⟨hx,hp⟩)
      | allFalse h =>
        exact .allFalse (by intro x hx hp; apply h x _ trivial; exact (restrict_mem C (.node l r) _ hu x).2 ⟨hx,hp⟩)
      | left h hn => exact .left (ihl _ el h) (by intro x hx hp; exact hn x ((restrict_mem C r _ er x).2 ⟨hx,hp⟩) trivial)
      | right hn h => exact .right (by intro x hx hp; exact hn x ((restrict_mem C l _ el x).2 ⟨hx,hp⟩) trivial) (ihr _ er h)

theorem selected_none (C : List Nat) (t : Tree)
    (h : ∀ x, x ∈ leaves t → x ∉ C) : ∀ a, ¬selectedLeaves C t a := by
  intro a ha
  obtain ⟨x,hx,hxa⟩ := (selected_decompose_label C t a).1 ha
  exact h x ((singleton_selected_exists t x).1 ⟨a,hxa⟩) hx

theorem reach_none {P : VertexGeometry.Vertex → Prop} (h : ∀ a, ¬P a) (v) : ¬Reach P v := by
  rintro ⟨a,ha,hp⟩; exact h a ha

theorem hull_none {P : VertexGeometry.Vertex → Prop} (h : ∀ a, ¬P a) (v) : ¬Hull P v := by
  rintro ⟨a,b,ha,hb,hp⟩; exact h a ha

/-- A rooted cluster of a final agreed block gives actual ORIGINAL-address
separation, including all unary paths. The stronger right side is rootedSpan. -/
theorem cluster_disjoint_span (C : List Nat) (q : Nat → Bool) (t : Tree)
    (hc : Cluster (fun x => x ∈ C) q t) :
    ∀ v, ¬(Hull (selectedLeaves (yes C q) t) v ∧ Reach (selectedLeaves (no C q) t) v) := by
  induction hc with
  | allTrue h =>
    have hn := selected_none (no C q) _ (by intro x hx hm; have hs := List.mem_filter.1 hm; have hq := h x hx hs.1; simp [no,hq] at hm)
    intro v hv; exact reach_none hn v hv.2
  | allFalse h =>
    have hn := selected_none (yes C q) _ (by intro x hx hm; have hs := List.mem_filter.1 hm; have hq := h x hx hs.1; simp [yes,hq] at hm)
    intro v hv; exact hull_none hn v hv.1
  | @left l r hc hn ih =>
    have hnr := selected_none (yes C q) r (by intro x hx hm; have hs := List.mem_filter.1 hm; have hq := hn x hx hs.1; simp [yes,hq] at hm)
    have hne : ¬VertexGeometry.Nonempty (selectedLeaves (yes C q) r) := by rintro ⟨a,ha⟩; exact hnr a ha
    intro v hv
    cases v with
    | nil => exact hne ((hull_join_root _ _).1 hv.1).2
    | cons s v => cases s with
      | false =>
        have hh := (hull_join_left _ _ v).1 hv.1
        have hh' : Hull (selectedLeaves (yes C q) l) v := hh.elim id (fun p => False.elim (hne p.2))
        exact ih v ⟨hh',(reach_join_side _ _ v).1 hv.2⟩
      | true =>
        rcases (hull_join_right _ _ v).1 hv.1 with hh | hh
        · exact hull_none hnr v hh
        · exact reach_none hnr v hh.1
  | @right l r hn hc ih =>
    have hnl := selected_none (yes C q) l (by intro x hx hm; have hs := List.mem_filter.1 hm; have hq := hn x hx hs.1; simp [yes,hq] at hm)
    have hne : ¬VertexGeometry.Nonempty (selectedLeaves (yes C q) l) := by rintro ⟨a,ha⟩; exact hnl a ha
    intro v hv
    cases v with
    | nil => exact hne ((hull_join_root _ _).1 hv.1).1
    | cons s v => cases s with
      | false =>
        rcases (hull_join_left _ _ v).1 hv.1 with hh | hh
        · exact hull_none hnl v hh
        · exact reach_none hnl v hh.1
      | true =>
        have hh := (hull_join_right _ _ v).1 hv.1
        have hh' : Hull (selectedLeaves (yes C q) r) v := hh.elim id (fun p => False.elim (hne p.2))
        exact ih v ⟨hh',(reach_join_right _ _ v).1 hv.2⟩

theorem cluster_disjoint (C : List Nat) (q : Nat → Bool) (t : Tree)
    (hc : Cluster (fun x => x ∈ C) q t) :
    disjointVertices (minimalVertices (yes C q) t) (minimalVertices (no C q) t) = true := by
  apply (executable_disjointVertices t _ _).2
  intro v hv
  exact cluster_disjoint_span C q t hc v ⟨hv.1,hull_subset_reach _ v hv.2⟩

/-- Core transfer: only this FINAL agreed C needs a rooted topology match.
No topology match is required for any original parent containing C. -/
theorem agreed_cluster_split (s t : Tree) (C : List Nat) (q : Nat → Bool)
    (ha : restrictionAgrees s t C = true)
    (ht : Cluster (fun x => x ∈ C) q t) :
    Cluster (fun x => x ∈ C) q s ∧
    disjointVertices (minimalVertices (yes C q) s) (minimalVertices (no C q) s) = true ∧
    disjointVertices (minimalVertices (yes C q) t) (minimalVertices (no C q) t) = true := by
  unfold restrictionAgrees at ha
  cases es : restrict C s <;> cases et : restrict C t <;> simp only [es,et] at ha
  all_goals try contradiction
  rename_i ss tt
  have hct := cluster_restrict ht C (fun x hx => hx) et
  have hcs := cluster_iso (iso_symm ((sameShape_correct ss tt).1 ha)) hct
  have hs := cluster_lift C q s ss es hcs
  exact ⟨hs,cluster_disjoint C q s hs,cluster_disjoint C q t ht⟩
end BinaryExchange
