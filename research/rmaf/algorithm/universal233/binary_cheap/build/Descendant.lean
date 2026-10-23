import Cluster
namespace BinaryExchange
open RMAF VertexGeometry

def treeAt : Tree → RMAF.Vertex → Option Tree
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .node l _, false :: v => treeAt l v
  | .node _ r, true :: v => treeAt r v

theorem treeAt_mem (t u : Tree) (v : RMAF.Vertex) (h : treeAt t v = some u) :
    ∀ x, x ∈ leaves u → x ∈ leaves t := by
  induction v generalizing t with
  | nil => simp only [treeAt, Option.some.injEq] at h; subst t; exact fun x hx => hx
  | cons s v ih =>
    cases t with
    | leaf x => simp [treeAt] at h
    | node l r => cases s with
      | false => intro x hx; exact List.mem_append_left _ (ih l h x hx)
      | true => intro x hx; exact List.mem_append_right _ (ih r h x hx)

theorem cluster_weaken {p p' : Nat → Prop} {q : Nat → Bool} {t : Tree}
    (h : Cluster p q t) (hp : ∀ x, p' x → p x) : Cluster p' q t := by
  induction h with
  | allTrue h => exact .allTrue (fun x hx hp' => h x hx (hp x hp'))
  | allFalse h => exact .allFalse (fun x hx hp' => h x hx (hp x hp'))
  | left h hn ih => exact .left ih (fun x hx hp' => hn x hx (hp x hp'))
  | right hn h ih => exact .right (fun x hx hp' => hn x hx (hp x hp')) ih

theorem subtree_cluster (t u : Tree) (v : RMAF.Vertex)
    (hn : (leaves t).Nodup) (h : treeAt t v = some u) :
    Cluster (fun _ => True) ((leaves u).contains ·) t := by
  induction v generalizing t with
  | nil =>
    have he : t = u := Option.some.inj (by simpa [treeAt] using h)
    subst u
    exact .allTrue (by intro x hx hp; simpa using hx)
  | cons s v ih =>
    cases t with
    | leaf x => simp [treeAt] at h
    | node l r =>
      obtain ⟨hl,hr,hd⟩ := List.nodup_append.1 hn
      cases s with
      | false =>
        exact .left (ih l hl h) (by
          intro x hx hp
          apply Bool.eq_false_iff.2
          intro hm
          exact hd x (treeAt_mem l u v h x (List.contains_iff_mem.1 hm)) x hx rfl)
      | true =>
        exact .right (by
          intro x hx hp
          apply Bool.eq_false_iff.2
          intro hm
          exact hd x hx x (treeAt_mem r u v h x (List.contains_iff_mem.1 hm)) rfl) (ih r hr h)

theorem treeAt_selected (t u : Tree) (v : RMAF.Vertex) (h : treeAt t v = some u)
    (C : List Nat) (a : RMAF.Vertex) :
    selectedLeaves C t (v ++ a) ↔ selectedLeaves C u a := by
  induction v generalizing t with
  | nil =>
    have he : t = u := Option.some.inj (by simpa [treeAt] using h)
    subst u
    rfl
  | cons s v ih =>
    cases t with
    | leaf x => simp [treeAt] at h
    | node l r => cases s with
      | false => exact ih l h
      | true => exact ih r h

theorem prefix_not_up (v a : RMAF.Vertex) : Prefix v a ↔ region v a ≠ 2 := by
  induction v generalizing a with
  | nil =>
    constructor
    · intro h; exact region_root_not_up a
    · intro h; exact ⟨a,rfl⟩
  | cons s v ih =>
    cases a with
    | nil => simp [Prefix,region]
    | cons t a =>
      by_cases he : s = t
      · subst t
        simpa [Prefix,region] using ih a
      · simp [Prefix,region,he,Ne.symm he]

theorem selected_descendant_iff (t u : Tree) (v a : RMAF.Vertex) (x : Nat)
    (hn : (leaves t).Nodup) (h : treeAt t v = some u)
    (ha : selectedLeaves [x] t a) : Prefix v a ↔ x ∈ leaves u := by
  constructor
  · rintro ⟨b,rfl⟩
    exact (singleton_selected_exists u x).1 ⟨b,(treeAt_selected t u v h [x] b).1 ha⟩
  · intro hx
    obtain ⟨b,hb⟩ := (singleton_selected_exists u x).2 hx
    have hab := singleton_selected_address_unique t x hn a (v ++ b) ha
      ((treeAt_selected t u v h [x] b).2 hb)
    exact ⟨b,hab⟩

/-- Every final block crossing a literal original descendant edge occupies its
child endpoint in the ACTUAL unsuppressed target embedding. -/
theorem crossing_occupies (t u : Tree) (v : RMAF.Vertex) (C : List Nat)
    (hn : (leaves t).Nodup) (h : treeAt t v = some u)
    (hC : ∀ x, x ∈ C → x ∈ leaves t)
    (hmix : (∃ x, x ∈ C ∧ x ∈ leaves u) ∧ (∃ y, y ∈ C ∧ y ∉ leaves u)) :
    v ∈ minimalVertices C t := by
  obtain ⟨⟨x,hx,hxu⟩,⟨y,hy,hyu⟩⟩ := hmix
  obtain ⟨a,ha⟩ := (singleton_selected_exists t x).2 (hC x hx)
  obtain ⟨b,hb⟩ := (singleton_selected_exists t y).2 (hC y hy)
  have hpa := (selected_descendant_iff t u v a x hn h ha).2 hxu
  have hpb : ¬Prefix v b := fun hpb => hyu ((selected_descendant_iff t u v b y hn h hb).1 hpb)
  have hra := (prefix_not_up v a).1 hpa
  have hrb : region v b = 2 := by
    by_cases he : region v b = 2
    · exact he
    · exact False.elim (hpb ((prefix_not_up v b).2 he))
  apply (minimalVertices_correct C t v).2
  exact ⟨a,b,(selected_decompose_label C t a).2 ⟨x,hx,ha⟩,
    (selected_decompose_label C t b).2 ⟨y,hy,hb⟩,
    region_ne_path v a b (by simpa only [hrb] using hra)⟩

/-- Literal original-edge cluster, transferred only for agreed FINAL C. -/
theorem descendant_agreed_split (s t u : Tree) (v : RMAF.Vertex) (C : List Nat)
    (hn : (leaves t).Nodup) (he : treeAt t v = some u)
    (ha : restrictionAgrees s t C = true) :
    Cluster (fun x => x ∈ C) ((leaves u).contains ·) s ∧
    disjointVertices (minimalVertices (yes C ((leaves u).contains ·)) s)
      (minimalVertices (no C ((leaves u).contains ·)) s) = true ∧
    disjointVertices (minimalVertices (yes C ((leaves u).contains ·)) t)
      (minimalVertices (no C ((leaves u).contains ·)) t) = true := by
  exact agreed_cluster_split s t C _ ha
    (cluster_weaken (subtree_cluster t u v hn he) (fun _ _ => trivial))
end BinaryExchange
