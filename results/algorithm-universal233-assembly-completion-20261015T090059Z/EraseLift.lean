import Suppression

/-! One-shot bridge from exact CoreProgram.erase on unique original origins
to proved actual graph leaf erasure and suppression. -/
namespace Universal233.Integration
open RMAF CoreGraph CoreProgram

def origins : GTree → List RMAF.Vertex
  | .leaf g => [g.origin]
  | .node p l r => p :: (origins l ++ origins r)

theorem groupLeaf_origin_mem (t : GTree) (v : RMAF.Vertex) (g : Group)
    (h : GroupLeafAt t v g) : g.origin ∈ origins t := by
  induction t generalizing v with
  | leaf a => obtain ⟨rfl,rfl⟩ := (groupLeaf_leaf a g v).1 h; simp [origins]
  | node p l r ihl ihr =>
    cases v with
    | nil => simp [GroupLeafAt,groupAt] at h
    | cons s v => cases s <;> simp only [origins,List.mem_cons,List.mem_append]
                             <;> first | exact Or.inr (Or.inl (ihl v h)) | exact Or.inr (Or.inr (ihr v h))

theorem erase_of_origin_absent (t : GTree) (chosen : RMAF.Vertex) (h : chosen ∉ origins t) :
    erase chosen t = some t := by
  induction t with
  | leaf g => simp_all [origins,erase,eq_comm]
  | node p l r ihl ihr =>
    have hp : p ≠ chosen := by intro he; apply h; simp [origins,he]
    have hl : chosen ∉ origins l := by intro hm; apply h; simp [origins,hm]
    have hr : chosen ∉ origins r := by intro hm; apply h; simp [origins,hm]
    simp [erase,hp,ihl hl,ihr hr]

inductive GLeafErase : GTree → GTree → RMAF.Vertex → Group → Type
  | rootLeft (p : RMAF.Vertex) (g : Group) (r : GTree) : GLeafErase (.node p (.leaf g) r) r [false] g
  | rootRight (p : RMAF.Vertex) (l : GTree) (g : Group) : GLeafErase (.node p l (.leaf g)) l [true] g
  | left {t u v g} (p : RMAF.Vertex) (r : GTree) : GLeafErase t u v g →
      GLeafErase (.node p t r) (.node p u r) (false :: v) g
  | right {t u v g} (p : RMAF.Vertex) (l : GTree) : GLeafErase t u v g →
      GLeafErase (.node p l t) (.node p l u) (true :: v) g

theorem erase_leaf_realization (t : GTree) (hn : (origins t).Nodup)
    (v : RMAF.Vertex) (g : Group) (hv : GroupLeafAt t v g) (hvr : v ≠ []) :
    ∃ u, erase g.origin t = some u ∧ Nonempty (GLeafErase t u v g) := by
  induction t generalizing v with
  | leaf a => obtain ⟨rfl,he⟩ := (groupLeaf_leaf a g v).1 hv; exact False.elim (hvr rfl)
  | node p l r ihl ihr =>
    have hnd := List.nodup_cons.1 hn
    obtain ⟨hnl,hnr,hdisj⟩ := List.nodup_append.1 hnd.2
    have hgm : g.origin ∈ origins l ++ origins r := by
      cases v with
      | nil => simp [GroupLeafAt,groupAt] at hv
      | cons s v =>
        cases s with
        | false => exact List.mem_append_left _ (groupLeaf_origin_mem l v g hv)
        | true => exact List.mem_append_right _ (groupLeaf_origin_mem r v g hv)
    have hgp : p ≠ g.origin := by intro he; subst p; exact hnd.1 hgm
    cases v with
    | nil => exact False.elim (hvr rfl)
    | cons s v =>
      cases s with
      | false =>
        have hgl := groupLeaf_origin_mem l v g hv
        have hgr : g.origin ∉ origins r := by intro hm; exact hdisj _ hgl _ hm rfl
        have her := erase_of_origin_absent r g.origin hgr
        by_cases hve : v = []
        · subst v
          cases l with
          | leaf a =>
            have he : a = g := (groupLeaf_leaf a g []).1 hv |>.2
            subst a
            exact ⟨r,by simp [erase,hgp,her],⟨.rootLeft p g r⟩⟩
          | node a b c => simp [GroupLeafAt,groupAt] at hv
        · obtain ⟨u,hu,⟨he⟩⟩ := ihl hnl v hv hve
          exact ⟨.node p u r,by simp [erase,hgp,hu,her],⟨.left p r he⟩⟩
      | true =>
        have hgr := groupLeaf_origin_mem r v g hv
        have hgl : g.origin ∉ origins l := by intro hm; exact hdisj _ hm _ hgr rfl
        have hel := erase_of_origin_absent l g.origin hgl
        by_cases hve : v = []
        · subst v
          cases r with
          | leaf a =>
            have he : a = g := (groupLeaf_leaf a g []).1 hv |>.2
            subst a
            exact ⟨l,by simp [erase,hgp,hel],⟨.rootRight p l g⟩⟩
          | node a b c => simp [GroupLeafAt,groupAt] at hv
        · obtain ⟨u,hu,⟨he⟩⟩ := ihr hnr v hv hve
          exact ⟨.node p l u,by simp [erase,hgp,hel,hu],⟨.right p l he⟩⟩

def gLeafErase_graph {t u v g} : GLeafErase t u v g → LeafErasure (skeleton t) (skeleton u)
  | .rootLeft _ g r => .rootLeft g.color (skeleton r)
  | .rootRight _ l g => .rootRight (skeleton l) g.color
  | .left _ r h => .left (skeleton r) (gLeafErase_graph h)
  | .right _ l h => .right (skeleton l) (gLeafErase_graph h)

theorem gLeafErase_group_lift {t u v g} (h : GLeafErase t u v g)
    (a : RMAF.Vertex) (b : Group) (hb : GroupLeafAt u a b) :
    GroupLeafAt t (erasureEmbedding (gLeafErase_graph h) a) b := by
  induction h generalizing a with
  | rootLeft => exact hb
  | rootRight => exact hb
  | left p r h ih =>
    cases a with
    | nil => simp [GroupLeafAt,groupAt] at hb
    | cons s a => cases s <;> first | exact ih a hb | exact hb
  | right p l h ih =>
    cases a with
    | nil => simp [GroupLeafAt,groupAt] at hb
    | cons s a => cases s <;> first | exact hb | exact ih a hb

theorem gLeafErase_group_survives {t u v g} (h : GLeafErase t u v g)
    (a : RMAF.Vertex) (b : Group) (hb : GroupLeafAt t a b) (hne : a ≠ v) :
    ∃ w, GroupLeafAt u w b ∧ erasureEmbedding (gLeafErase_graph h) w = a := by
  induction h generalizing a with
  | rootLeft p g r =>
    cases a with
    | nil => simp [GroupLeafAt,groupAt] at hb
    | cons s a =>
      cases s with
      | false => obtain ⟨rfl,he⟩ := (groupLeaf_leaf g b a).1 hb; exact False.elim (hne rfl)
      | true => exact ⟨a,hb,rfl⟩
  | rootRight p l g =>
    cases a with
    | nil => simp [GroupLeafAt,groupAt] at hb
    | cons s a =>
      cases s with
      | false => exact ⟨a,hb,rfl⟩
      | true => obtain ⟨rfl,he⟩ := (groupLeaf_leaf g b a).1 hb; exact False.elim (hne rfl)
  | left p r h ih =>
    cases a with
    | nil => simp [GroupLeafAt,groupAt] at hb
    | cons s a =>
      cases s with
      | false =>
        obtain ⟨w,hw,he⟩ := ih a hb (by intro he; exact hne (congrArg (false :: ·) he))
        exact ⟨false :: w,hw,congrArg (false :: ·) he⟩
      | true => exact ⟨true :: a,hb,rfl⟩
  | right p l h ih =>
    cases a with
    | nil => simp [GroupLeafAt,groupAt] at hb
    | cons s a =>
      cases s with
      | false => exact ⟨false :: a,hb,rfl⟩
      | true =>
        obtain ⟨w,hw,he⟩ := ih a hb (by intro he; exact hne (congrArg (true :: ·) he))
        exact ⟨true :: w,hw,congrArg (true :: ·) he⟩

theorem gLeafErase_embedding_avoids {t u v g} (h : GLeafErase t u v g) (a : RMAF.Vertex) :
    erasureEmbedding (gLeafErase_graph h) a ≠ v := by
  induction h generalizing a with
  | rootLeft => simp [gLeafErase_graph,erasureEmbedding]
  | rootRight => simp [gLeafErase_graph,erasureEmbedding]
  | left p r h ih =>
    cases a with
    | nil => simp [gLeafErase_graph,erasureEmbedding]
    | cons s a => cases s <;> simp [gLeafErase_graph,erasureEmbedding,ih]
  | right p l h ih =>
    cases a with
    | nil => simp [gLeafErase_graph,erasureEmbedding]
    | cons s a => cases s <;> simp [gLeafErase_graph,erasureEmbedding,ih]

/-- Exact executable erase consumer with actual suppression, original payload
lift, surviving block equality, and complete exclusion of the detached block. -/
theorem erase_leaf_source_transport (t : GTree) (hn : (origins t).Nodup)
    (v : RMAF.Vertex) (g : Group) (hv : GroupLeafAt t v g) (hvr : v ≠ [])
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id) (hs : SingletonBlock P v) :
    ∃ u, erase g.origin t = some u ∧ ∃ Q : SourcePartition (skeleton u),
      Monochromatic Q id ∧ ∃ e : RMAF.Vertex → RMAF.Vertex,
      (∀ a b, GroupLeafAt u a b → GroupLeafAt t (e a) b ∧ Q.owner a = P.owner (e a)) ∧
      (∀ a b, GroupLeafAt t a b → a ≠ v → ∃ w, GroupLeafAt u w b ∧ e w = a) ∧
      (∀ a b, GroupLeafAt u a b → Q.owner a ≠ P.owner v) := by
  obtain ⟨u,hu,⟨h⟩⟩ := erase_leaf_realization t hn v g hv hvr
  let eh := gLeafErase_graph h
  let Q := erasePartition eh P
  refine ⟨u,hu,Q,erasePartition_monochromatic eh P id hm,erasureEmbedding eh,?_,?_,?_⟩
  · intro a b hb
    exact ⟨gLeafErase_group_lift h a b hb,rfl⟩
  · exact gLeafErase_group_survives h
  · intro a b hb ho
    have hl := groupLeaf_skeleton t _ b (gLeafErase_group_lift h a b hb)
    exact gLeafErase_embedding_avoids h a (hs _ _ hl ho)

end Universal233.Integration
