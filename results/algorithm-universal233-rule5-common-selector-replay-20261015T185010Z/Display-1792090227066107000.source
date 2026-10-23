import OriginalGraph
import CoreInvariants

/-! One-shot derivation of original-live-leaf payload semantics. `Models` is an
induction invariant proved from fromTree/normalize/erase, never an input assumed
for an original residual-component or production-output theorem. -/
namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration

def rootOrigin : GTree → RMAF.Vertex
  | .leaf g => g.origin
  | .node p _ _ => p

def Exact (T : Tree) (cuts : List RMAF.Vertex) (base : RMAF.Vertex) (L : List Nat) : Prop :=
  ∀ a x, LeafAt T a x → (x ∈ L ↔ Pre base a ∧ Live cuts a)

def LabelsValid (T : Tree) (L : List Nat) : Prop :=
  ∀ x, x ∈ L → ∃ a, LeafAt T a x

def Difference (old next removed : List Nat) : Prop :=
  ∀ x, x ∈ next ↔ x ∈ old ∧ x ∉ removed

structure Facts (T : Tree) (cuts : List RMAF.Vertex) (base : RMAF.Vertex) (t : GTree) : Prop where
  under : Pre base (rootOrigin t)
  actual : Valid T (rootOrigin t)
  live : Live cuts (rootOrigin t)
  exactBase : Exact T cuts base (payload t)
  exactRoot : Exact T cuts (rootOrigin t) (payload t)
  labelsValid : LabelsValid T (payload t)
  nonempty : payload t ≠ []

inductive Models (T : Tree) (cuts : List RMAF.Vertex) : RMAF.Vertex → GTree → Prop
  | leaf (base : RMAF.Vertex) (g : Group) : Facts T cuts base (.leaf g) → Models T cuts base (.leaf g)
  | node (base p : RMAF.Vertex) (l r : GTree) : Facts T cuts base (.node p l r) →
      Models T cuts (p ++ [false]) l → Models T cuts (p ++ [true]) r →
      Models T cuts base (.node p l r)

theorem Models.facts {T cuts base t} (h : Models T cuts base t) : Facts T cuts base t := by
  cases h with
  | leaf _ _ f => exact f
  | node _ _ _ _ f _ _ => exact f

theorem models_rebase {T cuts base t} (h : Models T cuts base t) (b : RMAF.Vertex)
    (hp : Pre b (rootOrigin t)) (he : Exact T cuts b (payload t)) : Models T cuts b t := by
  cases h with
  | leaf _ g f => exact .leaf b g { f with under := hp, exactBase := he }
  | node _ p l r f hl hr => exact .node b p l r { f with under := hp, exactBase := he } hl hr

theorem exact_after_cut {T cuts base q old next removed}
    (he : Exact T cuts base old) (hg : Exact T cuts q removed)
    (hd : Difference old next removed) : Exact T (q :: cuts) base next := by
  intro a x ha
  rw [hd x,he a x ha,hg a x ha,live_cons]
  constructor
  · rintro ⟨⟨hb,hl⟩,hn⟩
    exact ⟨hb,(fun hp => hn ⟨hp,hl⟩),hl⟩
  · rintro ⟨hb,hn,hl⟩
    exact ⟨⟨hb,hl⟩,fun hq => hn hq.1⟩

theorem live_from_exact {T cuts base L} (he : Exact T cuts base L)
    (hv : LabelsValid T L) (hn : L ≠ []) : Live cuts base := by
  cases L with
  | nil => exact False.elim (hn rfl)
  | cons x xs =>
    obtain ⟨a,ha⟩ := hv x (by simp)
    have hx := (he a x ha).1 (by simp)
    exact live_ancestor hx.2 hx.1

theorem facts_after_same {T cuts base t u q removed}
    (f : Facts T cuts base t) (hr : rootOrigin u = rootOrigin t)
    (hg : Exact T cuts q removed) (hd : Difference (payload t) (payload u) removed)
    (hne : payload u ≠ []) : Facts T (q :: cuts) base u := by
  have heb := exact_after_cut f.exactBase hg hd
  have her : Exact T (q :: cuts) (rootOrigin u) (payload u) := by
    rw [hr]
    exact exact_after_cut f.exactRoot hg hd
  have hv : LabelsValid T (payload u) := fun x hx => f.labelsValid x ((hd x).1 hx).1
  exact ⟨hr ▸ f.under,hr ▸ f.actual,live_from_exact her hv hne,heb,her,hv,hne⟩

theorem payload_groups (t : GTree) : payload t = (groups t).flatMap Group.labels := by
  induction t with
  | leaf g => simp [payload,groups]
  | node p l r ihl ihr => simp [payload,groups,ihl,ihr]

theorem fromTree_root (color : Nat → Nat) (p : RMAF.Vertex) (t : Tree) :
    rootOrigin (fromTree color p t) = p := by cases t <;> rfl

theorem fromTree_payload (color : Nat → Nat) (p : RMAF.Vertex) (t : Tree) :
    payload (fromTree color p t) = leaves t := by
  induction t generalizing p with
  | leaf x => rfl
  | node l r ihl ihr => simp [fromTree,payload,leaves,ihl,ihr]

theorem subtree_leaf_iff {T s : Tree} {p a : RMAF.Vertex} {x : Nat}
    (hs : subtree T p = some s) (ha : LeafAt T a x) (hn : (leaves T).Nodup) :
    x ∈ leaves s ↔ Pre p a := by
  constructor
  · intro hx
    obtain ⟨q,hq⟩ := leaf_exists hx
    have hl : LeafAt T (p ++ q) x := by
      unfold LeafAt
      rw [subtree_append hs]
      exact hq
    have he := leaf_unique hn ha hl
    rw [he]
    exact List.prefix_append p q
  · rintro ⟨q,hq⟩
    subst a
    have hl : LeafAt s q x := by
      unfold LeafAt at *
      rwa [subtree_append hs] at ha
    exact leafAt_label s q x hl

theorem fromTree_facts (color : Nat → Nat) {T s : Tree} {p : RMAF.Vertex}
    (hn : (leaves T).Nodup) (hs : subtree T p = some s) :
    Facts T [] p (fromTree color p s) := by
  have he : Exact T [] p (payload (fromTree color p s)) := by
    intro a x ha
    rw [fromTree_payload]
    simpa using subtree_leaf_iff hs ha hn
  have hv : LabelsValid T (payload (fromTree color p s)) := by
    intro x hx
    rw [fromTree_payload] at hx
    obtain ⟨a,ha⟩ := leaf_exists hx
    exact ⟨p ++ a,by unfold LeafAt; rw [subtree_append hs]; exact ha⟩
  have hne : payload (fromTree color p s) ≠ [] := by
    rw [fromTree_payload]; exact leaves_nonempty s
  exact ⟨by simp [fromTree_root],by simpa [fromTree_root] using (show Valid T p from ⟨s,hs⟩),
    live_nil _,he,by simpa [fromTree_root] using he,hv,hne⟩

theorem fromTree_models (color : Nat → Nat) {T s : Tree} {p : RMAF.Vertex}
    (hn : (leaves T).Nodup) (hs : subtree T p = some s) :
    Models T [] p (fromTree color p s) := by
  induction s generalizing p with
  | leaf x => exact .leaf p _ (fromTree_facts color hn hs)
  | node l r ihl ihr =>
    exact .node p p _ _ (fromTree_facts color hn hs)
      (ihl (by simpa [subtree] using subtree_append hs [false]))
      (ihr (by simpa [subtree] using subtree_append hs [true]))

theorem normalize_root (t : GTree) : rootOrigin (normalize t) = rootOrigin t := by
  cases t with
  | leaf g => rfl
  | node p l r =>
    cases hl : normalize l <;> cases hr : normalize r <;> simp only [normalize,hl,hr]
    all_goals first | split <;> rfl | rfl

theorem normalize_facts {T cuts base t} (h : Facts T cuts base t) :
    Facts T cuts base (normalize t) := by
  have hp := normalize_payload t
  have hr := normalize_root t
  exact ⟨by simpa only [hr] using h.under,by simpa only [hr] using h.actual,
    by simpa only [hr] using h.live,by simpa only [hp] using h.exactBase,
    by simpa only [hp,hr] using h.exactRoot,by simpa only [hp] using h.labelsValid,
    by simpa only [hp] using h.nonempty⟩

theorem normalize_models {T cuts base t} (h : Models T cuts base t) :
    Models T cuts base (normalize t) := by
  induction h with
  | leaf b g f => exact .leaf b g f
  | node b p l r f hl hr ihl ihr =>
    have ff := normalize_facts f
    cases el : normalize l with
    | leaf a =>
      cases er : normalize r with
      | leaf c =>
        by_cases hc : a.color = c.color
        · simp only [normalize,el,er,if_pos hc] at ff ⊢
          exact .leaf b _ ff
        · simp only [normalize,el,er,if_neg hc] at ff ⊢
          exact .node b p _ _ ff (el ▸ ihl) (er ▸ ihr)
      | node q a c =>
        simp only [normalize,el,er] at ff ⊢
        exact .node b p _ _ ff (el ▸ ihl) (er ▸ ihr)
    | node q a c =>
      cases er : normalize r <;> simp only [normalize,el,er] at ff ⊢
      all_goals exact .node b p _ _ ff (el ▸ ihl) (er ▸ ihr)

theorem gleaf_payload_perm {t u v g} (h : GLeafErase t u v g) :
    (payload t).Perm (g.labels ++ payload u) := by
  induction h with
  | rootLeft => exact .refl _
  | rootRight => exact List.perm_append_comm
  | left p r h ih => simpa [payload,List.append_assoc] using ih.append_right (payload r)
  | @right t u v g p l h ih =>
    have one := List.Perm.append_left (payload l) ih
    have two := (List.perm_append_comm (l₁ := payload l) (l₂ := g.labels)).append_right (payload u)
    exact one.trans (by simpa [payload,List.append_assoc] using two)

theorem gleaf_difference {t u v g} (h : GLeafErase t u v g) (hn : (payload t).Nodup) :
    Difference (payload t) (payload u) g.labels := by
  have hp := gleaf_payload_perm h
  have hd := (List.nodup_append.1 (hp.nodup hn)).2.2
  intro x
  rw [hp.mem_iff,List.mem_append]
  constructor
  · intro hx
    exact ⟨Or.inr hx,fun hg => hd x hg x hx rfl⟩
  · rintro ⟨hh,hg⟩
    exact hh.resolve_left hg

theorem models_add_unchanged {T cuts base t q removed} (h : Models T cuts base t)
    (hg : Exact T cuts q removed) (hd : ∀ x, x ∈ payload t → x ∉ removed) :
    Models T (q :: cuts) base t := by
  induction h with
  | leaf b g f =>
    exact .leaf b g (facts_after_same f rfl hg (fun x => ⟨fun hx => ⟨hx,hd x hx⟩,fun hx => hx.1⟩) f.nonempty)
  | node b p l r f hl hr ihl ihr =>
    exact .node b p l r
      (facts_after_same f rfl hg (fun x => ⟨fun hx => ⟨hx,hd x hx⟩,fun hx => hx.1⟩) f.nonempty)
      (ihl (fun x hx => hd x (List.mem_append_left _ hx)))
      (ihr (fun x hx => hd x (List.mem_append_right _ hx)))

theorem group_model {T cuts base t} (h : Models T cuts base t)
    {v : RMAF.Vertex} {g : Group} (hv : GroupLeafAt t v g) :
    ∃ b, Models T cuts b (.leaf g) := by
  induction h generalizing v with
  | leaf b a f =>
    obtain ⟨rfl,rfl⟩ := (groupLeaf_leaf a g v).1 hv
    exact ⟨b,.leaf b _ f⟩
  | node b p l r f hl hr ihl ihr =>
    cases v with
    | nil => simp [GroupLeafAt,groupAt] at hv
    | cons s v => cases s <;> first | exact ihl hv | exact ihr hv

theorem gleaf_models {T cuts base t u v g} (e : GLeafErase t u v g)
    (h : Models T cuts base t) (hn : (payload t).Nodup)
    (hg : Exact T cuts g.origin g.labels) : Models T (g.origin :: cuts) base u := by
  induction e generalizing base with
  | rootLeft p g r =>
    cases h with
    | node b _ _ _ f hl hr =>
      have hnd := List.nodup_append.1 hn
      have hd : ∀ x, x ∈ payload r → x ∉ g.labels := by
        intro x hx hgx; exact hnd.2.2 x hgx x hx rfl
      have hh := models_add_unchanged hr hg hd
      exact models_rebase hh base
        (f.under.trans ((List.prefix_append p [true]).trans hr.facts.under))
        (exact_after_cut f.exactBase hg (gleaf_difference (.rootLeft p g r) hn))
  | rootRight p l g =>
    cases h with
    | node b _ _ _ f hl hr =>
      have hnd := List.nodup_append.1 hn
      have hd : ∀ x, x ∈ payload l → x ∉ g.labels := by
        intro x hx hgx; exact hnd.2.2 x hx x hgx rfl
      have hh := models_add_unchanged hl hg hd
      exact models_rebase hh base
        (f.under.trans ((List.prefix_append p [false]).trans hl.facts.under))
        (exact_after_cut f.exactBase hg (gleaf_difference (.rootRight p l g) hn))
  | @left t u v g p r e ih =>
    cases h with
    | node b _ _ _ f hl hr =>
      have hnd := List.nodup_append.1 hn
      have hp := gleaf_payload_perm e
      have hd : ∀ x, x ∈ payload r → x ∉ g.labels := by
        intro x hx hgx
        exact hnd.2.2 x (hp.mem_iff.2 (List.mem_append_left _ hgx)) x hx rfl
      have hh := ih hl hnd.1 hg
      have rr := models_add_unchanged hr hg hd
      apply Models.node base p _ _
      · apply facts_after_same (u := .node p u r) f rfl hg (gleaf_difference (.left p r e) hn)
        intro he
        exact hh.facts.nonempty (List.append_eq_nil_iff.1 he).1
      · exact hh
      · exact rr
  | @right t u v g p l e ih =>
    cases h with
    | node b _ _ _ f hl hr =>
      have hnd := List.nodup_append.1 hn
      have hp := gleaf_payload_perm e
      have hd : ∀ x, x ∈ payload l → x ∉ g.labels := by
        intro x hx hgx
        exact hnd.2.2 x hx x (hp.mem_iff.2 (List.mem_append_left _ hgx)) rfl
      have hh := ih hr hnd.2.1 hg
      have ll := models_add_unchanged hl hg hd
      apply Models.node base p _ _
      · apply facts_after_same (u := .node p l u) f rfl hg (gleaf_difference (.right p l e) hn)
        intro he
        exact hh.facts.nonempty (List.append_eq_nil_iff.1 he).2
      · exact ll
      · exact hh

end Universal233.CutRealization
