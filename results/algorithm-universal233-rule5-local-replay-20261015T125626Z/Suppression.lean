import InitialLift

/-! One-shot actual graph semantics of leaf deletion and unary suppression.
Source supports are recanonicalized as terminal hulls, so leafless excursions
cannot become false collisions when a unary parent is suppressed. -/
namespace Universal233.Integration
open RMAF CoreGraph VertexGeometry

theorem region_child_same (target a : RMAF.Vertex) (s : Bool)
    (ha : a ≠ target) (hb : a ++ [s] ≠ target) :
    region target a = region target (a ++ [s]) := by
  induction a generalizing target with
  | nil =>
    cases target with
    | nil => exact False.elim (ha rfl)
    | cons b target =>
      cases target with
      | nil => cases b <;> cases s <;> simp_all [region]
      | cons c target => simp [region]
  | cons b a ih =>
    cases target with
    | nil => cases b <;> rfl
    | cons c target =>
      by_cases h : c = b
      · subst c
        simpa [region] using ih target (by intro he; exact ha (congrArg (b :: ·) he))
          (by intro he; exact hb (congrArg (b :: ·) he))
      · simp [region,h]

theorem region_adj_same {t : Tree} {target a b : RMAF.Vertex} (h : Adj t a b)
    (ha : a ≠ target) (hb : b ≠ target) : region target a = region target b := by
  rcases h.2.2 with ⟨s,rfl⟩ | ⟨s,rfl⟩
  · exact region_child_same target a s ha hb
  · exact (region_child_same target b s hb ha).symm

theorem walk_avoids_region {t : Tree} {P : RMAF.Vertex → Prop} {a b target : RMAF.Vertex}
    (h : Walk t P a b) (hn : ¬P target) : region target a = region target b := by
  induction h with
  | refl => rfl
  | @step a b c hp ha tail ih =>
    have hna : a ≠ target := by intro he; subst target; exact hn hp
    have hnb : b ≠ target := by intro he; subst target; exact hn tail.start
    exact (region_adj_same ha hna hnb).trans ih

/-- Connectedness in the actual one-edge source graph entails address convexity;
this is derived from the Walk constructors, not assumed for source partitions. -/
theorem source_support_convex {t : Tree} (P : SourcePartition t) (i : Nat) :
    Convex (P.support i) := by
  intro v a b ha hb hp
  apply Classical.byContradiction
  intro hn
  have hna : a ≠ v := by intro he; subst a; exact hn ha
  have hnb : b ≠ v := by intro he; subst b; exact hn hb
  exact path_region_ne v a b hp hna hnb
    (walk_avoids_region (P.connected i a b ha hb) hn)

theorem invalid_region (t : Tree) (v a : RMAF.Vertex) (hn : ¬Valid t v) (ha : Valid t a) :
    region v a = 2 := by
  induction t generalizing v a with
  | leaf x =>
    have he := valid_leaf_only x a ha
    subst a
    cases v with
    | nil => exact False.elim (hn (valid_root _))
    | cons b v => rfl
  | node l r ihl ihr =>
    cases v with
    | nil => exact False.elim (hn (valid_root _))
    | cons s v =>
      cases a with
      | nil => rfl
      | cons z a =>
        cases s <;> cases z
        · exact ihl v a hn ha
        · rfl
        · rfl
        · exact ihr v a hn ha

theorem valid_convex (t : Tree) : Convex (Valid t) := by
  intro v a b ha hb hp
  apply Classical.byContradiction
  intro hn
  have hna : a ≠ v := by intro he; subst a; exact hn ha
  have hnb : b ≠ v := by intro he; subst b; exact hn hb
  exact path_region_ne v a b hp hna hnb
    ((invalid_region t v a hn ha).trans (invalid_region t v b hn hb).symm)

/-- Actual leaf deletion followed by suppression of its now-unary parent. -/
inductive LeafErasure : Tree → Tree → Type
  | rootLeft (x : Nat) (r : Tree) : LeafErasure (.node (.leaf x) r) r
  | rootRight (l : Tree) (x : Nat) : LeafErasure (.node l (.leaf x)) l
  | left {t u} (r : Tree) : LeafErasure t u → LeafErasure (.node t r) (.node u r)
  | right {t u} (l : Tree) : LeafErasure t u → LeafErasure (.node l t) (.node l u)

def erasureEmbedding {t u : Tree} : LeafErasure t u → RMAF.Vertex → RMAF.Vertex
  | .rootLeft _ _, v => true :: v
  | .rootRight _ _, v => false :: v
  | .left _ _, [] => []
  | .left _ h, false :: v => false :: erasureEmbedding h v
  | .left _ _, true :: v => true :: v
  | .right _ _, [] => []
  | .right _ _, false :: v => false :: v
  | .right _ h, true :: v => true :: erasureEmbedding h v

theorem erasure_leaf {t u} (h : LeafErasure t u) (v : RMAF.Vertex) (x : Nat)
    (hv : LeafAt u v x) : LeafAt t (erasureEmbedding h v) x := by
  induction h generalizing v with
  | rootLeft => exact hv
  | rootRight => exact hv
  | left r h ih =>
    cases v with
    | nil => simp [LeafAt,subtree] at hv
    | cons s v => cases s <;> first | exact ih v hv | exact hv
  | right l h ih =>
    cases v with
    | nil => simp [LeafAt,subtree] at hv
    | cons s v => cases s <;> first | exact hv | exact ih v hv

theorem erasure_root_path {t u} (h : LeafErasure t u) (v a : RMAF.Vertex)
    (hp : PathAt v a []) : PathAt (erasureEmbedding h v) (erasureEmbedding h a) [] := by
  induction h generalizing v a with
  | rootLeft => exact .leftLeg true hp
  | rootRight => exact .leftLeg false hp
  | left r h ih =>
    cases hp with
    | endpointL a => exact .endpointL _ []
    | endpointR a => exact .endpointR _ []
    | leftLeg s hp =>
      cases s with
      | false => exact .leftLeg false (ih _ _ hp)
      | true => exact .leftLeg true hp
  | right l h ih =>
    cases hp with
    | endpointL a => exact .endpointL _ []
    | endpointR a => exact .endpointR _ []
    | leftLeg s hp =>
      cases s with
      | false => exact .leftLeg false hp
      | true => exact .leftLeg true (ih _ _ hp)

/-- Suppression embeds every new path in the unsuppressed original path. -/
theorem erasure_path {t u} (h : LeafErasure t u) (v a b : RMAF.Vertex)
    (hp : PathAt v a b) :
    PathAt (erasureEmbedding h v) (erasureEmbedding h a) (erasureEmbedding h b) := by
  induction h generalizing v a b with
  | rootLeft => exact .down true hp
  | rootRight => exact .down false hp
  | left r h ih =>
    cases hp with
    | endpointL => exact .endpointL _ _
    | endpointR => exact .endpointR _ _
    | fork a b => exact .fork _ _
    | fork' a b => exact .fork' _ _
    | down s hp => cases s with
      | false => exact .down false (ih _ _ _ hp)
      | true => exact .down true hp
    | leftLeg s hp => cases s with
      | false => exact .leftLeg false (erasure_root_path h _ _ hp)
      | true => exact .leftLeg true hp
    | rightLeg s hp => cases s with
      | false => exact .rightLeg false (path_sym (erasure_root_path h _ _ (path_sym hp)))
      | true => exact .rightLeg true hp
    | crossLeft s hp => cases s with
      | false => exact .crossLeft false (erasure_root_path h _ _ hp)
      | true => exact .crossLeft true hp
    | crossRight s hp => cases s with
      | false => exact .crossRight false (path_sym (erasure_root_path h _ _ (path_sym hp)))
      | true => exact .crossRight true hp
  | right l h ih =>
    cases hp with
    | endpointL => exact .endpointL _ _
    | endpointR => exact .endpointR _ _
    | fork a b => exact .fork _ _
    | fork' a b => exact .fork' _ _
    | down s hp => cases s with
      | false => exact .down false hp
      | true => exact .down true (ih _ _ _ hp)
    | leftLeg s hp => cases s with
      | false => exact .leftLeg false hp
      | true => exact .leftLeg true (erasure_root_path h _ _ hp)
    | rightLeg s hp => cases s with
      | false => exact .rightLeg false hp
      | true => exact .rightLeg true (path_sym (erasure_root_path h _ _ (path_sym hp)))
    | crossLeft s hp => cases s with
      | false => exact .crossLeft false hp
      | true => exact .crossLeft true (erasure_root_path h _ _ hp)
    | crossRight s hp => cases s with
      | false => exact .crossRight false hp
      | true => exact .crossRight true (path_sym (erasure_root_path h _ _ (path_sym hp)))

def erasureTerminals {t u} (h : LeafErasure t u) (P : SourcePartition t) (i : Nat)
    (v : RMAF.Vertex) : Prop := ∃ x, LeafAt u v x ∧ P.owner (erasureEmbedding h v) = i

theorem erasureHull_actual {t u} (h : LeafErasure t u) (P : SourcePartition t)
    (i : Nat) (v : RMAF.Vertex) (hv : Hull (erasureTerminals h P i) v) : Valid u v := by
  obtain ⟨a,b,⟨x,ha,hoa⟩,⟨y,hb,hob⟩,hp⟩ := hv
  exact valid_convex u v a b ha.valid hb.valid hp

theorem erasureHull_image {t u} (h : LeafErasure t u) (P : SourcePartition t)
    (i : Nat) (v : RMAF.Vertex) (hv : Hull (erasureTerminals h P i) v) :
    P.support i (erasureEmbedding h v) := by
  obtain ⟨a,b,⟨x,ha,hoa⟩,⟨y,hb,hob⟩,hp⟩ := hv
  exact source_support_convex P i _ _ _
    ((P.terminal_exact _ _ _ (erasure_leaf h a x ha)).2 hoa)
    ((P.terminal_exact _ _ _ (erasure_leaf h b y hb)).2 hob)
    (erasure_path h v a b hp)

/-- Constructed valid source partition on the actual suppressed binary graph.
Leafless support excursions are removed by a terminal hull construction. -/
def erasePartition {t u} (h : LeafErasure t u) (P : SourcePartition t) : SourcePartition u where
  owner := fun v => P.owner (erasureEmbedding h v)
  support := fun i => Hull (erasureTerminals h P i)
  actual := erasureHull_actual h P
  terminal_exact := by
    intro i v x hv
    constructor
    · intro hs
      exact (P.terminal_exact i _ x (erasure_leaf h v x hv)).1 (erasureHull_image h P i v hs)
    · intro ho
      exact ⟨v,v,⟨x,hv,ho⟩,⟨x,hv,ho⟩,.endpointL v v⟩
  connected := by
    intro i a b ha hb
    exact convex_connected u _ (hull_convex _) a b
      (erasureHull_actual h P i a ha) (erasureHull_actual h P i b hb) ha hb
  disjoint := by
    intro i j v hi hj
    exact P.disjoint _ _ _ (erasureHull_image h P i v hi) (erasureHull_image h P j v hj)

theorem erasePartition_monochromatic {t u} (h : LeafErasure t u) (P : SourcePartition t)
    (color : Nat → Nat) (hm : Monochromatic P color) :
    Monochromatic (erasePartition h P) color := by
  intro a b x y ha hb ho
  exact hm _ _ _ _ (erasure_leaf h a x ha) (erasure_leaf h b y hb) ho

end Universal233.Integration
