import Controls
namespace OrdinaryCommonSplit
open RMAF

def relabel (f : Nat → Nat) : Tree → Tree
  | .leaf x => .leaf (f x)
  | .node a b => .node (relabel f a) (relabel f b)

def relabelForest (f : Nat → Nat) (F : List (List Nat)) := F.map (List.map f)

def swap (a b x : Nat) := if x=a then b else if x=b then a else x

theorem swap_involution (a b x : Nat) : swap a b (swap a b x)=x := by
  by_cases ha : x=a
  · subst x;by_cases he : a=b <;> simp [swap,he]
  · by_cases hb : x=b
    · subst x;simp [swap,ha]
    · simp [swap,ha,hb]

theorem swap_injective (a b x y : Nat) (h : swap a b x=swap a b y) : x=y := by
  have hh := congrArg (swap a b) h
  simpa only [swap_involution] using hh

theorem leaves_relabel (f : Nat → Nat) (t : Tree) : leaves (relabel f t)=(leaves t).map f := by
  induction t with
  | leaf x => rfl
  | node a b ha hb => simp [relabel,leaves,ha,hb]

theorem relabel_twice (f : Nat → Nat) (inv : ∀ x, f (f x)=x) (t : Tree) :
    relabel f (relabel f t)=t := by
  induction t with
  | leaf x => simp [relabel,inv]
  | node a b ha hb => simp [relabel,ha,hb]

theorem relabel_iso (f : Nat → Nat) {t s : Tree} (h : RootedIso t s) :
    RootedIso (relabel f t) (relabel f s) := by
  induction h with
  | leaf x => exact .leaf _
  | straight h1 h2 ih1 ih2 => exact .straight ih1 ih2
  | swapped h1 h2 ih1 ih2 => exact .swapped ih1 ih2

theorem sameShape_relabel_swap (a b : Nat) (t s : Tree) :
    sameShape (relabel (swap a b) t) (relabel (swap a b) s)=sameShape t s := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    have hh := relabel_iso (swap a b) ((sameShape_correct _ _).1 h)
    rw [relabel_twice _ (swap_involution a b),relabel_twice _ (swap_involution a b)] at hh
    exact (sameShape_correct _ _).2 hh
  · intro h
    exact (sameShape_correct _ _).2 (relabel_iso (swap a b) ((sameShape_correct _ _).1 h))

theorem contains_relabel (f : Nat → Nat) (inj : ∀ x y, f x=f y → x=y)
    (B : List Nat) (x : Nat) : (B.map f).contains (f x)=B.contains x := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem,List.mem_map]
  constructor
  · rintro ⟨y,hy,he⟩
    have hx : y=x := inj y x he
    simpa [hx] using hy
  · intro hx;exact ⟨x,hx,rfl⟩

theorem restrict_relabel (f : Nat → Nat) (inj : ∀ x y, f x=f y → x=y)
    (B : List Nat) (t : Tree) :
    restrict (B.map f) (relabel f t)=(restrict B t).map (relabel f) := by
  induction t with
  | leaf x => simp only [relabel,restrict,contains_relabel f inj];split <;> rfl
  | node a b ha hb =>
    simp only [relabel,restrict,ha,hb]
    cases h1 : restrict B a <;> cases h2 : restrict B b <;> rfl

theorem rootedSpan_relabel (f : Nat → Nat) (inj : ∀ x y, f x=f y → x=y)
    (B : List Nat) (t : Tree) : rootedSpan (B.map f) (relabel f t)=rootedSpan B t := by
  induction t with
  | leaf x => simp only [relabel,rootedSpan,contains_relabel f inj]
  | node a b ha hb => simp only [relabel,rootedSpan,ha,hb]

theorem minimal_relabel (f : Nat → Nat) (inj : ∀ x y, f x=f y → x=y)
    (B : List Nat) (t : Tree) : minimalVertices (B.map f) (relabel f t)=minimalVertices B t := by
  induction t with
  | leaf x => simp only [relabel,minimalVertices,contains_relabel f inj]
  | node a b ha hb =>
    simp only [relabel,minimalVertices,rootedSpan_relabel f inj,ha,hb]

theorem embeddings_relabel (f : Nat → Nat) (inj : ∀ x y, f x=f y → x=y)
    (F : List (List Nat)) (t : Tree) :
    pairwiseEmbeddings (relabel f t) (relabelForest f F)=pairwiseEmbeddings t F := by
  induction F with
  | nil => rfl
  | cons B F ih =>
    change ((F.map (List.map f)).all (fun C => disjointVertices
      (minimalVertices (B.map f) (relabel f t)) (minimalVertices C (relabel f t))) &&
      pairwiseEmbeddings (relabel f t) (relabelForest f F))=_
    rw [ih]
    simp only [minimal_relabel f inj,List.all_map]
    congr 1
    apply List.all_congr rfl
    intro C
    simp only [Function.comp_def]
    rw [minimal_relabel f inj]

theorem count_relabel (f : Nat → Nat) (inj : ∀ x y, f x=f y → x=y)
    (B : List Nat) (x : Nat) : (B.map f).count (f x)=B.count x := by
  induction B with
  | nil => rfl
  | cons y B ih =>
    have he : (f y==f x)=(y==x) := by
      apply Bool.eq_iff_iff.2
      simp only [beq_iff_eq]
      exact ⟨inj y x,congrArg f⟩
    simp only [List.map_cons,List.count_cons,he,ih]

theorem partition_relabel (f : Nat → Nat) (inj : ∀ x y, f x=f y → x=y)
    (L : List Nat) (F : List (List Nat)) :
    partitionCheck (L.map f) (relabelForest f F)=partitionCheck L F := by
  have flat : (relabelForest f F).flatten=F.flatten.map f := (List.map_flatten).symm
  simp only [partitionCheck]
  rw [flat]
  simp only [relabelForest,List.all_map,List.isEmpty_map,
    Function.comp_def,count_relabel f inj,contains_relabel f inj]

theorem agreement_relabel_swap (a b : Nat) (T S : Tree) (F : List (List Nat)) :
    agreement (relabel (swap a b) T) (relabel (swap a b) S) (relabelForest (swap a b) F)=
      agreement T S F := by
  have topo : (relabelForest (swap a b) F).all (restrictionAgrees (relabel (swap a b) T)
      (relabel (swap a b) S))=F.all (restrictionAgrees T S) := by
    simp only [relabelForest,List.all_map]
    apply List.all_congr rfl
    intro B
    simp only [Function.comp_def,restrictionAgrees,restrict_relabel _ (swap_injective a b)]
    cases ht : restrict B T <;> cases hs : restrict B S <;> simp [sameShape_relabel_swap]
  simp only [agreement,leaves_relabel,partition_relabel _ (swap_injective a b),
    embeddings_relabel _ (swap_injective a b),topo]

end OrdinaryCommonSplit
