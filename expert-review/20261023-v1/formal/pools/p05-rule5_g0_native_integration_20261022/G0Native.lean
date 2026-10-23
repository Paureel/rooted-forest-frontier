import PaidCaller
import Forest

namespace GenericG0Exchange
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.CherryBranching Universal233.Case322Extraction
open Universal233.Case322PaidGuard VertexGeometry

theorem leaves_nonempty (t : Tree) : leaves t ≠ [] := by
  induction t with
  | leaf a => simp [leaves]
  | node l r ihl ihr => simp [leaves, ihl]

theorem subtree_leaves_sublist (t : Tree) (p : RMAF.Vertex) (u : Tree)
    (h : subtree t p = some u) : List.Sublist (leaves u) (leaves t) := by
  induction p generalizing t with
  | nil =>
    simp only [subtree, Option.some.injEq] at h
    subst u
    exact List.Sublist.refl _
  | cons b p ih =>
    cases t with
    | leaf a => simp [subtree] at h
    | node l r =>
      cases b with
      | false => exact (ih l h).trans (List.sublist_append_left _ _)
      | true => exact (ih r h).trans (List.sublist_append_right _ _)

theorem source_label_separation {T S : Tree} (D : LiteralGeometry T S) :
    D.a ≠ D.b ∧ D.a ≠ D.c ∧ D.b ≠ D.c ∧
    D.a ∉ leaves D.X ∧ D.b ∉ leaves D.X ∧ D.c ∉ leaves D.X := by
  have hn := (subtree_leaves_sublist S D.w _ D.source).nodup D.properS
  cases ha : D.sa <;> cases hc : D.sc <;> cases hb : D.sb <;>
    simp_all [bottom, VC, AX, orient, leaves, List.nodup_append] <;> grind

theorem subtree_append (t : Tree) (p q : RMAF.Vertex) :
    subtree t (p ++ q) = (subtree t p).bind (fun u => subtree u q) := by
  induction p generalizing t with
  | nil => rfl
  | cons b p ih =>
    cases t with
    | leaf a => rfl
    | node l r => cases b <;> simp [subtree, ih]

theorem source_b_address {T S : Tree} (D : LiteralGeometry T S) :
    LeafAt S (bArc D.w D.sb) D.b := by
  unfold LeafAt bArc
  rw [subtree_append, D.source]
  cases hb : D.sb <;> simp [bottom, orient, subtree]

theorem source_c_address {T S : Tree} (D : LiteralGeometry T S) :
    LeafAt S (cArc D.w D.sc D.sb) D.c := by
  unfold LeafAt cArc
  rw [subtree_append, D.source]
  cases hb : D.sb <;> cases hc : D.sc <;>
    simp [bottom, VC, orient, subtree]

theorem source_x_address {T S : Tree} (D : LiteralGeometry T S) :
    subtree S (xArc D.w D.sa D.sc D.sb) = some D.X := by
  unfold xArc
  rw [subtree_append, D.source]
  cases hb : D.sb <;> cases hc : D.sc <;> cases ha : D.sa <;>
    simp [bottom, VC, AX, orient, subtree]

theorem partition_flat_coverage (L : List Nat) (G : List (List Nat))
    (h : partitionCheck L G = true) : ∀ x ∈ G.flatten, x ∈ L := by
  simp only [partitionCheck, Bool.and_eq_true] at h
  intro x hx
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h.2 x hx)

theorem partition_flat_nodup (L : List Nat) (G : List (List Nat))
    (h : partitionCheck L G = true) : G.flatten.Nodup := by
  have cov := partition_flat_coverage L G h
  simp only [partitionCheck, Bool.and_eq_true] at h
  apply List.nodup_iff_count_of_mem.mpr
  intro x hx
  exact (beq_iff_eq.mp (List.all_eq_true.mp h.1.2 x (cov x hx)))

theorem singleton_block_isolated (G : List (List Nat)) (b : Nat)
    (hn : G.flatten.Nodup) (hb : [b] ∈ G) :
    ∀ P ∈ G, b ∈ P → P = [b] := by
  induction G with
  | nil => simp at hb
  | cons R Rs ih =>
    simp only [List.flatten_cons, List.nodup_append] at hn
    simp only [List.mem_cons] at hb
    intro P hP hbp
    simp only [List.mem_cons] at hP
    rcases hb with hr | ht
    · subst R
      rcases hP with hp | hp
      · exact hp
      · exact False.elim (hn.2.2 b (by simp) b (List.mem_flatten.mpr ⟨P,hp,hbp⟩) rfl)
    · rcases hP with hp | hp
      · subst P
        exact False.elim (hn.2.2 b hbp b (List.mem_flatten.mpr ⟨[b],ht,by simp⟩) rfl)
      · exact ih hn.2.1 ht P hp hbp

theorem agreement_refines_b_singleton {T S : Tree} (G : List (List Nat)) (b : Nat)
    (h : agreement T S G = true) (hb : [b] ∈ G) :
    Refines G (singletonPartition S b) := by
  have hs : partitionCheck (leaves S) G = true := by
    simp only [agreement, Bool.and_eq_true] at h
    exact h.1.1.1.2
  have iso := singleton_block_isolated G b (partition_flat_nodup _ _ hs) hb
  have cov := partition_flat_coverage _ _ hs
  intro P hP
  by_cases hbp : b ∈ P
  · have hEq := iso P hP hbp
    refine ⟨[b], by simp [singletonPartition], ?_⟩
    intro x hx
    simpa [hEq] using hx
  · refine ⟨(leaves S).filter (fun x => x != b), by simp [singletonPartition], ?_⟩
    intro x hx
    have hxs := cov x (List.mem_flatten.mpr ⟨P,hP,hx⟩)
    have hxb : x ≠ b := by intro he; subst x; exact hbp hx
    simp [hxs, hxb]

-- This is a proved prefix only. No G0 theorem, branch admission, AF surgery,
-- source/native equivalence, or actual selected-caller composition is asserted.
#print axioms source_label_separation
#print axioms source_b_address
#print axioms source_c_address
#print axioms source_x_address
#print axioms agreement_refines_b_singleton
end GenericG0Exchange

namespace G0Resume
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.CherryBranching Universal233.Case322Extraction
open Universal233.Case322PaidGuard VertexGeometry GenericG0Exchange

theorem rooted_root_of_selected (P : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hp : x ∈ P) : ([] : RMAF.Vertex) ∈ rootedSpan P t := by
  induction t with
  | leaf a =>
    have hxa : x = a := by simpa [leaves] using hx
    subst x
    simp [rootedSpan, hp]
  | node l r ihl ihr =>
    have hs : rootedSpan P l ≠ [] ∨ rootedSpan P r ≠ [] := by
      rcases List.mem_append.mp hx with hxl | hxr
      · exact Or.inl (by intro he; have := ihl hxl; simp [he] at this)
      · exact Or.inr (by intro he; have := ihr hxr; simp [he] at this)
    simp only [rootedSpan]
    split
    · rename_i h
      simp only [Bool.and_eq_true, List.isEmpty_iff] at h
      rcases hs with hs | hs
      · exact False.elim (hs h.1)
      · exact False.elim (hs h.2)
    · simp

theorem minimal_subset_rooted (P : List Nat) (t : Tree) :
    ∀ v ∈ minimalVertices P t, v ∈ rootedSpan P t := by
  induction t with
  | leaf a => simp [minimalVertices, rootedSpan]
  | node l r ihl ihr =>
    cases hl : rootedSpan P l <;> cases hr : rootedSpan P r <;>
      simp_all [minimalVertices, rootedSpan, prependSide] <;> grind

theorem rooted_lift_left (P : List Nat) (l r : Tree) (v : RMAF.Vertex)
    (h : v ∈ rootedSpan P l) : false :: v ∈ rootedSpan P (.node l r) := by
  have hn : rootedSpan P l ≠ [] := by intro he; simp [he] at h
  simp [rootedSpan, hn, prependSide, h]

theorem rooted_lift_right (P : List Nat) (l r : Tree) (v : RMAF.Vertex)
    (h : v ∈ rootedSpan P r) : true :: v ∈ rootedSpan P (.node l r) := by
  have hn : rootedSpan P r ≠ [] := by intro he; simp [he] at h
  simp [rootedSpan, hn, prependSide, h]

theorem minimal_lift_left (P : List Nat) (l r : Tree) (v : RMAF.Vertex)
    (h : v ∈ minimalVertices P l) : false :: v ∈ minimalVertices P (.node l r) := by
  have hr := minimal_subset_rooted P l v h
  have hn : rootedSpan P l ≠ [] := by intro he; simp [he] at hr
  by_cases hh : rootedSpan P r = []
  · simp [minimalVertices, hn, hh, prependSide, h]
  · simp [minimalVertices, hn, hh, prependSide, hr]

theorem minimal_lift_right (P : List Nat) (l r : Tree) (v : RMAF.Vertex)
    (h : v ∈ minimalVertices P r) : true :: v ∈ minimalVertices P (.node l r) := by
  have hr := minimal_subset_rooted P r v h
  have hn : rootedSpan P r ≠ [] := by intro he; simp [he] at hr
  by_cases hh : rootedSpan P l = []
  · simp [minimalVertices, hn, hh, prependSide, h]
  · simp [minimalVertices, hn, hh, prependSide, hr]

theorem rooted_subtree_root (P : List Nat) (t u : Tree) (p : RMAF.Vertex)
    (h : subtree t p = some u) (x : Nat) (hx : x ∈ leaves u) (hp : x ∈ P) :
    p ∈ rootedSpan P t := by
  induction p generalizing t with
  | nil =>
    simp only [subtree, Option.some.injEq] at h
    subst u
    exact rooted_root_of_selected P t x hx hp
  | cons s p ih =>
    cases t with
    | leaf a => simp [subtree] at h
    | node l r =>
      cases s with
      | false => exact rooted_lift_left P l r p (ih l h)
      | true => exact rooted_lift_right P l r p (ih r h)

-- No AF or occurrence-uniqueness theorem is assumed here. The connector is
-- proved directly by following the cherry address through the tree.
theorem cherry_parent_mem (P : List Nat) (t : Tree) (p : RMAF.Vertex)
    (a b x : Nat) (hc : CherryAt t p a b) (ha : a ∈ P)
    (hx : x ∈ leaves t) (hxp : x ∈ P) (hne : x ≠ a) :
    p ∈ minimalVertices P t := by
  induction p generalizing t with
  | nil =>
    simp only [CherryAt, subtree, Option.some.injEq] at hc
    subst t
    have hxb : x = b := by simpa [leaves, hne] using hx
    subst x
    simp [minimalVertices, rootedSpan, ha, hxp]
  | cons s p ih =>
    cases t with
    | leaf z => simp [CherryAt, subtree] at hc
    | node l r =>
      cases s with
      | false =>
        have hcl : CherryAt l p a b := hc
        by_cases hxl : x ∈ leaves l
        · exact minimal_lift_left P l r p (ih l hcl hxl)
        · have hxr : x ∈ leaves r := (List.mem_append.mp hx).resolve_left hxl
          have hl := rooted_subtree_root P l (.node (.leaf a) (.leaf b)) p hcl a (by simp [leaves]) ha
          have hr := rooted_root_of_selected P r x hxr hxp
          have hln : rootedSpan P l ≠ [] := by intro he; simp [he] at hl
          have hrn : rootedSpan P r ≠ [] := by intro he; simp [he] at hr
          simp [minimalVertices, hln, hrn, prependSide, hl]
      | true =>
        have hcr : CherryAt r p a b := hc
        by_cases hxr : x ∈ leaves r
        · exact minimal_lift_right P l r p (ih r hcr hxr)
        · have hxl : x ∈ leaves l := (List.mem_append.mp hx).resolve_right hxr
          have hr := rooted_subtree_root P r (.node (.leaf a) (.leaf b)) p hcr a (by simp [leaves]) ha
          have hl := rooted_root_of_selected P l x hxl hxp
          have hln : rootedSpan P l ≠ [] := by intro he; simp [he] at hl
          have hrn : rootedSpan P r ≠ [] := by intro he; simp [he] at hr
          simp [minimalVertices, hln, hrn, prependSide, hr]

#print axioms cherry_parent_mem
end G0Resume

namespace G0Resume
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.CherryBranching Universal233.Case322Extraction
open Universal233.Case322PaidGuard VertexGeometry GenericG0Exchange

theorem cherry_parent_mem_right (P : List Nat) (t : Tree) (p : RMAF.Vertex)
    (a b x : Nat) (hc : CherryAt t p a b) (hb : b ∈ P)
    (hx : x ∈ leaves t) (hxp : x ∈ P) (hne : x ≠ b) :
    p ∈ minimalVertices P t := by
  induction p generalizing t with
  | nil =>
    simp only [CherryAt, subtree, Option.some.injEq] at hc
    subst t
    have hxa : x = a := by simpa [leaves, hne] using hx
    subst x
    simp [minimalVertices, rootedSpan, hb, hxp]
  | cons s p ih =>
    cases t with
    | leaf z => simp [CherryAt, subtree] at hc
    | node l r =>
      cases s with
      | false =>
        have hcl : CherryAt l p a b := hc
        by_cases hxl : x ∈ leaves l
        · exact minimal_lift_left P l r p (ih l hcl hxl)
        · have hxr : x ∈ leaves r := (List.mem_append.mp hx).resolve_left hxl
          have hl := rooted_subtree_root P l (.node (.leaf a) (.leaf b)) p hcl b (by simp [leaves]) hb
          have hr := rooted_root_of_selected P r x hxr hxp
          have hln : rootedSpan P l ≠ [] := by intro he; simp [he] at hl
          have hrn : rootedSpan P r ≠ [] := by intro he; simp [he] at hr
          simp [minimalVertices, hln, hrn, prependSide, hl]
      | true =>
        have hcr : CherryAt r p a b := hc
        by_cases hxr : x ∈ leaves r
        · exact minimal_lift_right P l r p (ih r hcr hxr)
        · have hxl : x ∈ leaves l := (List.mem_append.mp hx).resolve_right hxr
          have hr := rooted_subtree_root P r (.node (.leaf a) (.leaf b)) p hcr b (by simp [leaves]) hb
          have hl := rooted_root_of_selected P l x hxl hxp
          have hln : rootedSpan P l ≠ [] := by intro he; simp [he] at hl
          have hrn : rootedSpan P r ≠ [] := by intro he; simp [he] at hr
          simp [minimalVertices, hln, hrn, prependSide, hr]

theorem pairwise_no_common (t : Tree) (G : List (List Nat))
    (h : pairwiseEmbeddings t G = true) (P Q : List Nat)
    (hP : P ∈ G) (hQ : Q ∈ G) (hne : P ≠ Q) (v : RMAF.Vertex)
    (hvP : v ∈ minimalVertices P t) (hvQ : v ∈ minimalVertices Q t) : False := by
  induction G with
  | nil => simp at hP
  | cons R Rs ih =>
    simp only [pairwiseEmbeddings, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hP hQ
    rcases hP with hP | hP
    · subst P
      have hQ : Q ∈ Rs := hQ.resolve_left (Ne.symm hne)
      have hd := List.all_eq_true.mp h.1 Q hQ
      have hv := List.all_eq_true.mp hd v hvP
      simpa [disjointVertices, List.contains_iff_mem, hvQ] using hv
    · rcases hQ with hQ | hQ
      · subst Q
        have hd := List.all_eq_true.mp h.1 P hP
        have hv := List.all_eq_true.mp hd v hvQ
        simpa [disjointVertices, List.contains_iff_mem, hvP] using hv
      · exact ih h.2 hP hQ

theorem partition_block_exists (L : List Nat) (G : List (List Nat))
    (h : partitionCheck L G = true) (x : Nat) (hx : x ∈ L) :
    ∃ P ∈ G, x ∈ P := by
  simp only [partitionCheck, Bool.and_eq_true] at h
  have hc : G.flatten.count x = 1 := beq_iff_eq.mp (List.all_eq_true.mp h.1.2 x hx)
  exact List.mem_flatten.mp (List.count_pos_iff.mp (by omega : 0 < G.flatten.count x))

theorem block_nodup (G : List (List Nat)) (hn : G.flatten.Nodup)
    (P : List Nat) (hP : P ∈ G) : P.Nodup := by
  induction G with
  | nil => simp at hP
  | cons R Rs ih =>
    simp only [List.flatten_cons, List.nodup_append] at hn
    rcases List.mem_cons.mp hP with he | ht
    · subst P; exact hn.1
    · exact ih hn.2.1 ht

theorem singleton_or_other (P : List Nat) (a : Nat) (hn : P.Nodup) (ha : a ∈ P) :
    P = [a] ∨ ∃ x ∈ P, x ≠ a := by
  cases P with
  | nil => simp at ha
  | cons z zs =>
    by_cases hz : z = a
    · subst z
      cases zs with
      | nil => exact Or.inl rfl
      | cons x xs =>
        have hne : x ≠ a := by
          intro he; subst x
          exact (List.nodup_cons.mp hn).1 (by simp)
        exact Or.inr ⟨x, by simp, hne⟩
    · exact Or.inr ⟨z, by simp, hz⟩

-- Actual AF component dichotomy: no shape-agreement or branch-survival fact
-- is used. Only the target partition and pairwise target embeddings are needed.
theorem cherry_component_dichotomy (T : Tree) (G : List (List Nat)) (a b : Nat)
    (hc : ActualCherry T a b) (hp : partitionCheck (leaves T) G = true)
    (he : pairwiseEmbeddings T G = true) :
    (∃ P ∈ G, a ∈ P ∧ b ∈ P) ∨ [a] ∈ G ∨ [b] ∈ G := by
  obtain ⟨p, hch⟩ := hc
  have hla : a ∈ leaves T := by
    rcases hch with hch | hch
    · exact (subtree_leaves_sublist T p _ hch).subset (by simp [leaves])
    · exact (subtree_leaves_sublist T p _ hch).subset (by simp [leaves])
  have hlb : b ∈ leaves T := by
    rcases hch with hch | hch
    · exact (subtree_leaves_sublist T p _ hch).subset (by simp [leaves])
    · exact (subtree_leaves_sublist T p _ hch).subset (by simp [leaves])
  obtain ⟨P,hP,haP⟩ := partition_block_exists _ _ hp a hla
  obtain ⟨Q,hQ,hbQ⟩ := partition_block_exists _ _ hp b hlb
  by_cases hsame : P = Q
  · subst Q; exact Or.inl ⟨P,hP,haP,hbQ⟩
  have hn := partition_flat_nodup _ _ hp
  rcases singleton_or_other P a (block_nodup G hn P hP) haP with hsing | ⟨x,hxP,hxa⟩
  · exact Or.inr (Or.inl (hsing ▸ hP))
  rcases singleton_or_other Q b (block_nodup G hn Q hQ) hbQ with hsing | ⟨y,hyQ,hyb⟩
  · exact Or.inr (Or.inr (hsing ▸ hQ))
  have hxT := partition_flat_coverage _ _ hp x (List.mem_flatten.mpr ⟨P,hP,hxP⟩)
  have hyT := partition_flat_coverage _ _ hp y (List.mem_flatten.mpr ⟨Q,hQ,hyQ⟩)
  have hvP : p ∈ minimalVertices P T := by
    rcases hch with hch | hch
    · exact cherry_parent_mem P T p a b x hch haP hxT hxP hxa
    · exact cherry_parent_mem_right P T p b a x hch haP hxT hxP hxa
  have hvQ : p ∈ minimalVertices Q T := by
    rcases hch with hch | hch
    · exact cherry_parent_mem_right Q T p a b y hch hbQ hyT hyQ hyb
    · exact cherry_parent_mem Q T p b a y hch hbQ hyT hyQ hyb
  exact False.elim (pairwise_no_common T G he P Q hP hQ hsame p hvP hvQ)

theorem agreement_cherry_dichotomy {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) :
    (∃ P ∈ G, D.a ∈ P ∧ D.b ∈ P) ∨ [D.a] ∈ G ∨ [D.b] ∈ G := by
  simp only [agreement, Bool.and_eq_true] at hg
  exact cherry_component_dichotomy T G D.a D.b D.cherry hg.1.1.1.1 hg.1.2

#print axioms pairwise_no_common
#print axioms cherry_component_dichotomy
#print axioms agreement_cherry_dichotomy
end G0Resume

namespace G0Resume
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.CherryBranching Universal233.Case322Extraction
open Universal233.Case322PaidGuard Universal233.Rule5Case322
open VertexGeometry GenericG0Exchange

theorem rooted_empty_of_disjoint (P : List Nat) (t : Tree)
    (h : ∀ x ∈ leaves t, x ∉ P) : rootedSpan P t = [] := by
  induction t with
  | leaf a => simp [rootedSpan, h a (by simp [leaves])]
  | node l r ihl ihr =>
    have hl := ihl (fun x hx => h x (List.mem_append_left _ hx))
    have hr := ihr (fun x hx => h x (List.mem_append_right _ hx))
    simp [rootedSpan, hl, hr]

theorem rooted_leaf_not_mem (P : List Nat) (t : Tree) (p : RMAF.Vertex) (b : Nat)
    (hleaf : LeafAt t p b) (hb : b ∉ P) : p ∉ rootedSpan P t := by
  induction p generalizing t with
  | nil =>
    simp only [LeafAt, subtree, Option.some.injEq] at hleaf
    subst t
    simp [rootedSpan, hb]
  | cons s p ih =>
    cases t with
    | leaf a => simp [LeafAt, subtree] at hleaf
    | node l r =>
      cases s with
      | false =>
        have hi := ih l hleaf
        simp only [rootedSpan]
        split <;> simp_all [prependSide]
      | true =>
        have hi := ih r hleaf
        simp only [rootedSpan]
        split <;> simp_all [prependSide]

theorem minimal_singleton_leaf (t : Tree) (p : RMAF.Vertex) (b : Nat)
    (hn : (leaves t).Nodup) (hleaf : LeafAt t p b) :
    minimalVertices [b] t = [p] := by
  induction p generalizing t with
  | nil =>
    simp only [LeafAt, subtree, Option.some.injEq] at hleaf
    subst t
    simp [minimalVertices]
  | cons s p ih =>
    cases t with
    | leaf a => simp [LeafAt, subtree] at hleaf
    | node l r =>
      simp only [leaves, List.nodup_append] at hn
      cases s with
      | false =>
        have hbl : b ∈ leaves l :=
          (subtree_leaves_sublist l p _ hleaf).subset (by simp [leaves])
        have hbr : b ∉ leaves r := by intro hb; exact hn.2.2 b hbl b hb rfl
        have hr : rootedSpan [b] r = [] := rooted_empty_of_disjoint [b] r (by
          intro x hx hxb; have he : x = b := by simpa using hxb
          subst x; exact hbr hx)
        have hlm := rooted_root_of_selected [b] l b hbl (by simp)
        have hln : rootedSpan [b] l ≠ [] := by intro he; simp [he] at hlm
        simp [minimalVertices, hr, hln, ih l hn.1 hleaf, prependSide]
      | true =>
        have hbr : b ∈ leaves r :=
          (subtree_leaves_sublist r p _ hleaf).subset (by simp [leaves])
        have hbl : b ∉ leaves l := by intro hb; exact hn.2.2 b hb b hbr rfl
        have hl : rootedSpan [b] l = [] := rooted_empty_of_disjoint [b] l (by
          intro x hx hxb; have he : x = b := by simpa using hxb
          subst x; exact hbl hx)
        simp [minimalVertices, hl, ih r hn.2.1 hleaf, prependSide]

theorem singleton_partition_check (L : List Nat) (b : Nat) (hn : L.Nodup)
    (hb : b ∈ L) (hc : L.filter (fun x => x != b) ≠ []) :
    partitionCheck L [[b], L.filter (fun x => x != b)] = true := by
  let Q := L.filter (fun x => x != b)
  have hqn : Q.Nodup := List.Pairwise.filter _ hn
  have hbn : b ∉ Q := by simp [Q]
  have hflat : ([[b], Q] : List (List Nat)).flatten.Nodup := by
    simpa using List.nodup_cons.mpr ⟨hbn,hqn⟩
  have hcov : ∀ x, x ∈ ([[b], Q] : List (List Nat)).flatten ↔ x ∈ L := by
    intro x
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append,
      List.mem_cons, Q, List.mem_filter, bne_iff_ne]
    grind
  change partitionCheck L [[b], Q] = true
  simp only [partitionCheck, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro P hP
    rcases List.mem_cons.mp hP with he | ht
    · subst P; rfl
    · have he : P = Q := by simpa using ht
      subst P
      cases hq : Q with
      | nil => exact False.elim (hc hq)
      | cons z zs => rfl
  · intro x hx
    exact beq_iff_eq.mpr (hflat.count_of_mem ((hcov x).mpr hx))
  · intro x hx
    exact List.contains_iff_mem.mpr ((hcov x).mp hx)

theorem singleton_partition_embeddings (t : Tree) (p : RMAF.Vertex) (b : Nat)
    (hn : (leaves t).Nodup) (hleaf : LeafAt t p b) :
    pairwiseEmbeddings t (singletonPartition t b) = true := by
  have hs := minimal_singleton_leaf t p b hn hleaf
  have hb : b ∉ (leaves t).filter (fun x => x != b) := by simp
  have hnot := rooted_leaf_not_mem ((leaves t).filter (fun x => x != b)) t p b hleaf hb
  have hm : p ∉ minimalVertices ((leaves t).filter (fun x => x != b)) t := by
    intro hp; exact hnot (minimal_subset_rooted _ _ _ hp)
  simp [singletonPartition, pairwiseEmbeddings, disjointVertices, hs, hm]

theorem subtreeLabels_of_leaf (t : Tree) (p : RMAF.Vertex) (b : Nat)
    (hleaf : LeafAt t p b) : subtreeLabels t p = [b] := by
  induction p generalizing t with
  | nil =>
    simp only [LeafAt, subtree, Option.some.injEq] at hleaf
    subst t; rfl
  | cons s p ih =>
    cases t with
    | leaf a => simp [LeafAt, subtree] at hleaf
    | node l r => cases s <;> exact ih _ hleaf

theorem singleton_arc_partition (t : Tree) (p : RMAF.Vertex) (b : Nat)
    (hn : (leaves t).Nodup) (hleaf : LeafAt t p b)
    (hc : (leaves t).filter (fun x => x != b) ≠ []) :
    arcPartition t [p] = singletonPartition t b := by
  have hb : b ∈ leaves t :=
    (subtree_leaves_sublist t p _ hleaf).subset (by simp [leaves])
  have hy : BinaryExchange.yes (leaves t) ([b].contains) = [b] := by
    have heq : ([b].contains) = (fun x => x == b) := by
      funext x; simp [Bool.beq_eq_decide_eq]
    unfold BinaryExchange.yes
    rw [heq, List.filter_beq, hn.count_of_mem hb]
    rfl
  have hno : BinaryExchange.no (leaves t) ([b].contains) = (leaves t).filter (fun x => x != b) := by
    simp [BinaryExchange.no, bne_eq, Bool.beq_eq_decide_eq]
  simp [arcPartition, arcPartitionFrom, splitForest, BinaryExchange.splitAll,
    BinaryExchange.split, subtreeLabels_of_leaf t p b hleaf, hy, hno, hc,
    singletonPartition]

theorem b_branch_guard (T S : Tree) (p : RMAF.Vertex) (b : Nat)
    (hn : (leaves S).Nodup) (hleaf : LeafAt S p b) (hp : p ≠ [])
    (hc : (leaves S).filter (fun x => x != b) ≠ []) :
    currentGuard T S (bBranch S b p) = true := by
  have hb : b ∈ leaves S :=
    (subtree_leaves_sublist S p _ hleaf).subset (by simp [leaves])
  have hpart := singleton_partition_check (leaves S) b hn hb hc
  have hemb := singleton_partition_embeddings S p b hn hleaf
  have harc := singleton_arc_partition S p b hn hleaf hc
  have hls : subtree S p = some (.leaf b) := hleaf
  have hemb' : pairwiseEmbeddings S [[b],(leaves S).filter (fun x => x != b)] = true := hemb
  simp [currentGuard, bBranch, current, paid, hp, hls,
    singletonPartition, hpart, hemb', harc]

theorem literal_b_branch_guard {T S : Tree} (D : LiteralGeometry T S) :
    currentGuard T S (bBranch S D.b (bArc D.w D.sb)) = true := by
  have hla : D.a ∈ leaves S := (D.same D.a).mp
    ((subtree_leaves_sublist T D.qa _ D.leafA).subset (by simp [leaves]))
  have hab := (source_label_separation D).1
  have hcomp : (leaves S).filter (fun x => x != D.b) ≠ [] := by
    intro he
    have hm : D.a ∈ (leaves S).filter (fun x => x != D.b) := by simp [hla, hab]
    simp [he] at hm
  exact b_branch_guard T S _ _ D.properS (source_b_address D) (by simp [bArc]) hcomp

theorem literal_b_branch_mem {T S : Tree} (D : LiteralGeometry T S) :
    bBranch S D.b (bArc D.w D.sb) ∈ guardedPlan D := by
  apply List.mem_filter.mpr
  refine ⟨?_, literal_b_branch_guard D⟩
  unfold literalPlan rawPlan
  split
  · simp [typeIBranches]
  · split <;> simp [typeIIBranches]

-- An actual G0 witness for the b-singleton case: H is the unchanged original AF.
theorem g0_of_b_singleton {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (hb : [D.b] ∈ G) :
    ∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧
      H.length ≤ G.length ∧ Refines H child.partition := by
  refine ⟨bBranch S D.b (bArc D.w D.sb), literal_b_branch_mem D, G, hg, Nat.le_refl _, ?_⟩
  exact agreement_refines_b_singleton G D.b hg hb

#print axioms literal_b_branch_guard
#print axioms literal_b_branch_mem
#print axioms g0_of_b_singleton
end G0Resume

namespace G0Resume
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.Case322PaidGuard VertexGeometry

-- Exact remaining mathematical cases, with no exchange conclusion assumed.
-- The left alternative is the original G0 witness; the right alternatives
-- are the two residual hypotheses that a later exchange proof must handle.
theorem g0_witness_or_two_remaining_cases {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) :
    (∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧
      H.length ≤ G.length ∧ Refines H child.partition) ∨
    ([D.b] ∉ G ∧ (∃ P ∈ G, D.a ∈ P ∧ D.b ∈ P)) ∨
    ([D.b] ∉ G ∧ ¬(∃ P ∈ G, D.a ∈ P ∧ D.b ∈ P) ∧ [D.a] ∈ G) := by
  by_cases hb : [D.b] ∈ G
  · exact Or.inl (g0_of_b_singleton D G hg hb)
  by_cases hs : ∃ P ∈ G, D.a ∈ P ∧ D.b ∈ P
  · exact Or.inr (Or.inl ⟨hb,hs⟩)
  have ha : [D.a] ∈ G := by
    rcases agreement_cherry_dichotomy D G hg with h | h | h
    · exact False.elim (hs h)
    · exact h
    · exact False.elim (hb h)
  exact Or.inr (Or.inr ⟨hb,hs,ha⟩)

#print axioms g0_witness_or_two_remaining_cases
end G0Resume

namespace G0Shared
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.Case322Extraction Universal233.Case322PaidGuard
open G0Resume GenericG0Exchange

theorem actual_cherry_leaf_false (a b z : Nat) : ¬ ActualCherry (.leaf z) a b := by
  intro ⟨p,h⟩
  cases p <;> simp [CherryAt, subtree] at h

theorem actual_cherry_node_iff (l r : Tree) (a b : Nat) :
    ActualCherry (.node l r) a b ↔
    (l = .leaf a ∧ r = .leaf b) ∨ (l = .leaf b ∧ r = .leaf a) ∨
    ActualCherry l a b ∨ ActualCherry r a b := by
  constructor
  · intro ⟨p,h⟩
    cases p with
    | nil =>
      simp only [CherryAt, subtree, Option.some.injEq, Tree.node.injEq] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    | cons s p =>
      cases s with
      | false => exact Or.inr (Or.inr (Or.inl ⟨p,h⟩))
      | true => exact Or.inr (Or.inr (Or.inr ⟨p,h⟩))
  · intro h
    rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩ | ⟨p,h⟩ | ⟨p,h⟩
    · subst l; subst r; exact ⟨[],Or.inl rfl⟩
    · subst l; subst r; exact ⟨[],Or.inr rfl⟩
    · exact ⟨false::p,h⟩
    · exact ⟨true::p,h⟩

theorem actual_cherry_labels (t : Tree) (a b : Nat) (h : ActualCherry t a b) :
    a ∈ leaves t ∧ b ∈ leaves t := by
  obtain ⟨p,h⟩ := h
  rcases h with h | h
  · exact ⟨(subtree_leaves_sublist t p _ h).subset (by simp [leaves]),
      (subtree_leaves_sublist t p _ h).subset (by simp [leaves])⟩
  · exact ⟨(subtree_leaves_sublist t p _ h).subset (by simp [leaves]),
      (subtree_leaves_sublist t p _ h).subset (by simp [leaves])⟩

theorem sameShape_leaf_eq (a : Nat) (t : Tree) (h : sameShape (.leaf a) t = true) :
    t = .leaf a := by
  cases t with
  | leaf z => have he : a = z := beq_iff_eq.mp h; subst z; rfl
  | node l r => simp [sameShape] at h

theorem sameShape_preserves_cherry (t u : Tree) (a b : Nat)
    (h : sameShape t u = true) (hc : ActualCherry t a b) : ActualCherry u a b := by
  induction t generalizing u with
  | leaf z => exact False.elim (actual_cherry_leaf_false a b z hc)
  | node l r ihl ihr =>
    cases u with
    | leaf z => simp [sameShape] at h
    | node v w =>
      simp only [sameShape, Bool.or_eq_true, Bool.and_eq_true] at h
      apply (actual_cherry_node_iff v w a b).mpr
      rcases (actual_cherry_node_iff l r a b).mp hc with ⟨hl,hr⟩ | ⟨hl,hr⟩ | hl | hr
      · subst l; subst r
        rcases h with h | h
        · exact Or.inl ⟨sameShape_leaf_eq a v h.1, sameShape_leaf_eq b w h.2⟩
        · exact Or.inr (Or.inl ⟨sameShape_leaf_eq b v h.2, sameShape_leaf_eq a w h.1⟩)
      · subst l; subst r
        rcases h with h | h
        · exact Or.inr (Or.inl ⟨sameShape_leaf_eq b v h.1, sameShape_leaf_eq a w h.2⟩)
        · exact Or.inl ⟨sameShape_leaf_eq a v h.2, sameShape_leaf_eq b w h.1⟩
      · rcases h with h | h
        · exact Or.inr (Or.inr (Or.inl (ihl v h.1 hl)))
        · exact Or.inr (Or.inr (Or.inr (ihl w h.1 hl)))
      · rcases h with h | h
        · exact Or.inr (Or.inr (Or.inr (ihr w h.2 hr)))
        · exact Or.inr (Or.inr (Or.inl (ihr v h.2 hr)))

theorem restrict_preserves_cherry (P : List Nat) (t : Tree) (a b : Nat)
    (ha : a ∈ P) (hb : b ∈ P) (hc : ActualCherry t a b) :
    ∃ u, restrict P t = some u ∧ ActualCherry u a b := by
  induction t with
  | leaf z => exact False.elim (actual_cherry_leaf_false a b z hc)
  | node l r ihl ihr =>
    rcases (actual_cherry_node_iff l r a b).mp hc with ⟨hl,hr⟩ | ⟨hl,hr⟩ | hl | hr
    · subst l; subst r
      exact ⟨.node (.leaf a) (.leaf b), by simp [restrict,ha,hb], ⟨[],Or.inl rfl⟩⟩
    · subst l; subst r
      exact ⟨.node (.leaf b) (.leaf a), by simp [restrict,ha,hb], ⟨[],Or.inr rfl⟩⟩
    · obtain ⟨v,hv,hvc⟩ := ihl hl
      cases hw : restrict P r with
      | none => exact ⟨v,by simp [restrict,hv,hw],hvc⟩
      | some w => exact ⟨.node v w,by simp [restrict,hv,hw],
          (actual_cherry_node_iff v w a b).mpr (Or.inr (Or.inr (Or.inl hvc)))⟩
    · obtain ⟨w,hw,hwc⟩ := ihr hr
      cases hv : restrict P l with
      | none => exact ⟨w,by simp [restrict,hv,hw],hwc⟩
      | some v => exact ⟨.node v w,by simp [restrict,hv,hw],
          (actual_cherry_node_iff v w a b).mpr (Or.inr (Or.inr (Or.inr hwc)))⟩

def optionLeaves : Option Tree → List Nat
  | none => []
  | some t => leaves t

theorem restricted_leaves (P : List Nat) (t : Tree) :
    optionLeaves (restrict P t) = (leaves t).filter P.contains := by
  induction t with
  | leaf a =>
    by_cases ha : a ∈ P <;> simp [restrict,leaves,optionLeaves,ha]
  | node l r ihl ihr =>
    cases hl : restrict P l <;> cases hr : restrict P r <;>
      simp_all [restrict, leaves, optionLeaves, List.filter_append]

theorem restricted_mem_iff (P : List Nat) (t u : Tree) (h : restrict P t = some u) (x : Nat) :
    x ∈ leaves u ↔ x ∈ leaves t ∧ x ∈ P := by
  have he := restricted_leaves P t
  simp only [h,optionLeaves] at he
  rw [he]
  simp

theorem restrict_some_of_selected (P : List Nat) (t : Tree) (x : Nat)
    (hx : x ∈ leaves t) (hp : x ∈ P) : ∃ u, restrict P t = some u := by
  cases h : restrict P t with
  | some u => exact ⟨u,rfl⟩
  | none =>
    have he := restricted_leaves P t
    have hm : x ∈ (leaves t).filter P.contains := by simp [hx,hp]
    simp only [h,optionLeaves] at he
    rw [←he] at hm
    simp at hm

theorem cherry_node_left_of_absent_right (l r : Tree) (a b : Nat)
    (ha : a ∉ leaves r) (hb : b ∉ leaves r) (hc : ActualCherry (.node l r) a b) :
    ActualCherry l a b := by
  rcases (actual_cherry_node_iff l r a b).mp hc with ⟨hl,hr⟩ | ⟨hl,hr⟩ | h | h
  · subst r; exact False.elim (hb (by simp [leaves]))
  · subst r; exact False.elim (ha (by simp [leaves]))
  · exact h
  · exact False.elim (ha (actual_cherry_labels r a b h).1)

theorem cherry_node_right_of_absent_left (l r : Tree) (a b : Nat)
    (ha : a ∉ leaves l) (hb : b ∉ leaves l) (hc : ActualCherry (.node l r) a b) :
    ActualCherry r a b := by
  rcases (actual_cherry_node_iff l r a b).mp hc with ⟨hl,hr⟩ | ⟨hl,hr⟩ | h | h
  · subst l; exact False.elim (ha (by simp [leaves]))
  · subst l; exact False.elim (hb (by simp [leaves]))
  · exact False.elim (ha (actual_cherry_labels l a b h).1)
  · exact h

theorem restriction_cherry_local (P : List Nat) (t u : Tree) (p : RMAF.Vertex)
    (a b : Nat) (hn : (leaves t).Nodup) (hsub : subtree t p = some u)
    (ha : a ∈ leaves u) (hb : b ∈ leaves u) (haP : a ∈ P) (hbP : b ∈ P)
    (z : Tree) (hz : restrict P t = some z) (hc : ActualCherry z a b) :
    ∃ v, restrict P u = some v ∧ ActualCherry v a b := by
  induction p generalizing t z with
  | nil =>
    simp only [subtree,Option.some.injEq] at hsub
    subst u; exact ⟨z,hz,hc⟩
  | cons s p ih =>
    cases t with
    | leaf y => simp [subtree] at hsub
    | node l r =>
      simp only [leaves,List.nodup_append] at hn
      cases s with
      | false =>
        have hal := (subtree_leaves_sublist l p u hsub).subset ha
        have hbl := (subtree_leaves_sublist l p u hsub).subset hb
        have har : a ∉ leaves r := by intro h; exact hn.2.2 a hal a h rfl
        have hbr : b ∉ leaves r := by intro h; exact hn.2.2 b hbl b h rfl
        obtain ⟨v,hv⟩ := restrict_some_of_selected P l a hal haP
        cases hw : restrict P r with
        | none =>
          have he : v = z := by simpa [restrict,hv,hw] using hz
          subst z
          exact ih l hn.1 hsub v hv hc
        | some w =>
          have he : Tree.node v w = z := by simpa [restrict,hv,hw] using hz
          subst z
          have haw : a ∉ leaves w := fun h => har ((restricted_mem_iff P r w hw a).mp h).1
          have hbw : b ∉ leaves w := fun h => hbr ((restricted_mem_iff P r w hw b).mp h).1
          exact ih l hn.1 hsub v hv (cherry_node_left_of_absent_right v w a b haw hbw hc)
      | true =>
        have har := (subtree_leaves_sublist r p u hsub).subset ha
        have hbr := (subtree_leaves_sublist r p u hsub).subset hb
        have hal : a ∉ leaves l := by intro h; exact hn.2.2 a h a har rfl
        have hbl : b ∉ leaves l := by intro h; exact hn.2.2 b h b hbr rfl
        obtain ⟨w,hw⟩ := restrict_some_of_selected P r a har haP
        cases hv : restrict P l with
        | none =>
          have he : w = z := by simpa [restrict,hv,hw] using hz
          subst z
          exact ih r hn.2.1 hsub w hw hc
        | some v =>
          have he : Tree.node v w = z := by simpa [restrict,hv,hw] using hz
          subst z
          have hav : a ∉ leaves v := fun h => hal ((restricted_mem_iff P l v hv a).mp h).1
          have hbv : b ∉ leaves v := fun h => hbl ((restricted_mem_iff P l v hv b).mp h).1
          exact ih r hn.2.1 hsub w hw (cherry_node_right_of_absent_left v w a b hav hbv hc)

theorem orient_leaf_cherry_forces (s : Bool) (v : Tree) (a b : Nat)
    (hb : b ∉ leaves v) (hne : a ≠ b)
    (hc : ActualCherry (orient s v (.leaf b)) a b) : v = .leaf a := by
  have hv : ¬ ActualCherry v a b := fun h => hb (actual_cherry_labels v a b h).2
  cases s <;> simp only [orient, Bool.false_eq_true, ↓reduceIte] at hc
  · rcases (actual_cherry_node_iff v (.leaf b) a b).mp hc with h | h | h | h
    · exact h.1
    · exact False.elim (hne (Tree.leaf.inj h.2).symm)
    · exact False.elim (hv h)
    · exact False.elim (actual_cherry_leaf_false a b b h)
  · rcases (actual_cherry_node_iff (.leaf b) v a b).mp hc with h | h | h | h
    · exact False.elim (hne (Tree.leaf.inj h.1).symm)
    · exact h.2
    · exact False.elim (actual_cherry_leaf_false a b b h)
    · exact False.elim (hv h)

theorem shared_block_excludes_pendants {T S : Tree} (D : LiteralGeometry T S)
    (P : List Nat) (haP : D.a ∈ P) (hbP : D.b ∈ P)
    (hagree : restrictionAgrees T S P = true) :
    ∀ x ∈ P, x ∉ leaves D.X ∧ x ≠ D.c := by
  have sep := source_label_separation D
  obtain ⟨t,ht,htc⟩ := restrict_preserves_cherry P T D.a D.b haP hbP D.cherry
  cases hs : restrict P S with
  | none => simp [restrictionAgrees,ht,hs] at hagree
  | some s =>
    have hshape : sameShape t s = true := by simpa [restrictionAgrees,ht,hs] using hagree
    have hsc := sameShape_preserves_cherry t s D.a D.b hshape htc
    have haB : D.a ∈ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) := by
      cases D.sa <;> cases D.sc <;> cases D.sb <;> simp [bottom,VC,AX,orient,leaves]
    have hbB : D.b ∈ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) := by
      cases D.sa <;> cases D.sc <;> cases D.sb <;> simp [bottom,VC,AX,orient,leaves]
    obtain ⟨z,hz,hzc⟩ := restriction_cherry_local P S _ D.w D.a D.b
      D.properS D.source haB hbB haP hbP s hs hsc
    have haVC : D.a ∈ leaves (VC D.sa D.sc D.a D.c D.X) := by
      cases D.sa <;> cases D.sc <;> simp [VC,AX,orient,leaves]
    have hbVC : D.b ∉ leaves (VC D.sa D.sc D.a D.c D.X) := by
      cases D.sa <;> cases D.sc <;> simp [VC,AX,orient,leaves] <;> grind
    obtain ⟨v,hv⟩ := restrict_some_of_selected P (VC D.sa D.sc D.a D.c D.X) D.a haVC haP
    have hbot : restrict P (bottom D.sa D.sc D.sb D.a D.b D.c D.X) =
        some (orient D.sb v (.leaf D.b)) := by
      cases D.sb <;> simp [bottom,orient,restrict,hv,hbP]
    have hez : orient D.sb v (.leaf D.b) = z := by simpa [hbot] using hz
    subst z
    have hbv : D.b ∉ leaves v := fun h => hbVC ((restricted_mem_iff P _ v hv D.b).mp h).1
    have he : v = .leaf D.a := orient_leaf_cherry_forces D.sb v D.a D.b hbv sep.1 hzc
    intro x hx
    constructor
    · intro hxX
      have hxVC : x ∈ leaves (VC D.sa D.sc D.a D.c D.X) := by
        cases D.sa <;> cases D.sc <;> simp [VC,AX,orient,leaves,hxX]
      have hxv := (restricted_mem_iff P _ v hv x).mpr ⟨hxVC,hx⟩
      have hxa : x = D.a := by simpa [he,leaves] using hxv
      subst x
      exact sep.2.2.2.1 hxX
    · intro hxc
      subst x
      have hcVC : D.c ∈ leaves (VC D.sa D.sc D.a D.c D.X) := by
        cases D.sa <;> cases D.sc <;> simp [VC,AX,orient,leaves]
      have hcv := (restricted_mem_iff P _ v hv D.c).mpr ⟨hcVC,hx⟩
      have hca : D.c = D.a := by simpa [he,leaves] using hcv
      exact sep.2.1 hca.symm

#print axioms sameShape_preserves_cherry
#print axioms restriction_cherry_local
#print axioms shared_block_excludes_pendants
end G0Shared

namespace G0Shared
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.CherryBranching
open G0Resume GenericG0Exchange VertexGeometry

theorem minimal_subtree_lift (P : List Nat) (t u : Tree) (p v : RMAF.Vertex)
    (hs : subtree t p = some u) (hm : v ∈ minimalVertices P u) :
    p ++ v ∈ minimalVertices P t := by
  induction p generalizing t with
  | nil =>
    simp only [subtree,Option.some.injEq] at hs
    subst u; exact hm
  | cons s p ih =>
    cases t with
    | leaf a => simp [subtree] at hs
    | node l r =>
      cases s with
      | false => exact minimal_lift_left P l r (p++v) (ih l hs)
      | true => exact minimal_lift_right P l r (p++v) (ih r hs)

theorem orient_minimal_bridge (P : List Nat) (A B : Tree) (s : Bool)
    (x y : Nat) (hx : x ∈ leaves A) (hy : y ∈ leaves B)
    (hxP : x ∈ P) (hyP : y ∈ P) :
    ([] : RMAF.Vertex) ∈ minimalVertices P (orient s A B) ∧
    ∀ v ∈ rootedSpan P A, s::v ∈ minimalVertices P (orient s A B) := by
  have ha := rooted_root_of_selected P A x hx hxP
  have hb := rooted_root_of_selected P B y hy hyP
  have han : rootedSpan P A ≠ [] := by intro he; simp [he] at ha
  have hbn : rootedSpan P B ≠ [] := by intro he; simp [he] at hb
  cases s <;> simp [orient,minimalVertices,han,hbn,prependSide]

theorem subtree_root_crossing (P : List Nat) (t u : Tree) (p : RMAF.Vertex)
    (hs : subtree t p = some u) (x y : Nat) (hx : x ∈ leaves u)
    (hxP : x ∈ P) (hy : y ∈ leaves t) (hyP : y ∈ P) (hyu : y ∉ leaves u) :
    p ∈ minimalVertices P t := by
  induction p generalizing t with
  | nil =>
    simp only [subtree,Option.some.injEq] at hs
    subst u; exact False.elim (hyu hy)
  | cons s p ih =>
    cases t with
    | leaf a => simp [subtree] at hs
    | node l r =>
      cases s with
      | false =>
        by_cases hyl : y ∈ leaves l
        · exact minimal_lift_left P l r p (ih l hs hyl)
        · have hyr := (List.mem_append.mp hy).resolve_left hyl
          have hl := rooted_subtree_root P l u p hs x hx hxP
          have hb := orient_minimal_bridge P l r false x y
            ((subtree_leaves_sublist l p u hs).subset hx) hyr hxP hyP
          exact hb.2 p hl
      | true =>
        by_cases hyr : y ∈ leaves r
        · exact minimal_lift_right P l r p (ih r hs hyr)
        · have hyl := (List.mem_append.mp hy).resolve_right hyr
          have hr := rooted_subtree_root P r u p hs x hx hxP
          have hb := orient_minimal_bridge P r l true x y
            ((subtree_leaves_sublist r p u hs).subset hx) hyl hxP hyP
          exact hb.2 p hr

theorem pendant_parent_crossing (P : List Nat) (t A B : Tree) (p : RMAF.Vertex)
    (s : Bool) (hs : subtree t p = some (orient s A B))
    (x y : Nat) (hx : x ∈ leaves A) (hxP : x ∈ P)
    (hy : y ∈ leaves t) (hyP : y ∈ P) (hya : y ∉ leaves A) :
    p ∈ minimalVertices P t := by
  by_cases hyb : y ∈ leaves B
  · have hm := (orient_minimal_bridge P A B s x y hx hyb hxP hyP).1
    simpa using minimal_subtree_lift P t (orient s A B) p [] hs hm
  · have hxo : x ∈ leaves (orient s A B) := by cases s <;> simp [orient,leaves,hx]
    have hyo : y ∉ leaves (orient s A B) := by cases s <;> simp [orient,leaves,hya,hyb]
    exact subtree_root_crossing P t _ p hs x y hxo hxP hy hyP hyo

theorem source_ax_address {T S : Tree} (D : LiteralGeometry T S) :
    subtree S (D.w ++ [D.sb,D.sc]) = some (AX D.sa D.a D.X) := by
  rw [GenericG0Exchange.subtree_append,D.source]
  cases D.sb <;> cases D.sc <;> simp [bottom,VC,orient,subtree]

theorem source_vc_address {T S : Tree} (D : LiteralGeometry T S) :
    subtree S (D.w ++ [D.sb]) = some (VC D.sa D.sc D.a D.c D.X) := by
  rw [GenericG0Exchange.subtree_append,D.source]
  cases D.sb <;> simp [bottom,orient,subtree]

theorem source_spine {T S : Tree} (D : LiteralGeometry T S) (P : List Nat)
    (ha : D.a ∈ P) (hb : D.b ∈ P) :
    D.w ∈ minimalVertices P S ∧
    D.w ++ [D.sb] ∈ minimalVertices P S ∧
    D.w ++ [D.sb,D.sc] ∈ minimalVertices P S := by
  have haVC : D.a ∈ leaves (VC D.sa D.sc D.a D.c D.X) := by
    cases D.sa <;> cases D.sc <;> simp [VC,AX,orient,leaves]
  have haAX : D.a ∈ leaves (AX D.sa D.a D.X) := by cases D.sa <;> simp [AX,orient,leaves]
  have hs : subtree (VC D.sa D.sc D.a D.c D.X) [D.sc] = some (AX D.sa D.a D.X) := by
    cases D.sc <;> simp [VC,orient,subtree]
  have hr0 := rooted_root_of_selected P (VC D.sa D.sc D.a D.c D.X) D.a haVC ha
  have hr1 := rooted_subtree_root P (VC D.sa D.sc D.a D.c D.X) _ [D.sc] hs D.a haAX ha
  have hm := orient_minimal_bridge P (VC D.sa D.sc D.a D.c D.X) (.leaf D.b) D.sb
    D.a D.b haVC (by simp [leaves]) ha hb
  exact ⟨by simpa [bottom] using minimal_subtree_lift P S _ D.w [] D.source hm.1,
    by simpa [bottom] using minimal_subtree_lift P S _ D.w [D.sb] D.source (hm.2 [] hr0),
    by simpa [bottom] using minimal_subtree_lift P S _ D.w [D.sb,D.sc] D.source (hm.2 [D.sc] hr1)⟩

theorem source_x_crossing {T S : Tree} (D : LiteralGeometry T S) (P : List Nat)
    (x y : Nat) (hxX : x ∈ leaves D.X) (hxP : x ∈ P)
    (hy : y ∈ leaves S) (hyP : y ∈ P) (hyX : y ∉ leaves D.X) :
    D.w ++ [D.sb,D.sc] ∈ minimalVertices P S := by
  have hs := source_ax_address D
  have he : AX D.sa D.a D.X = orient (!D.sa) D.X (.leaf D.a) := by cases D.sa <;> rfl
  rw [he] at hs
  exact pendant_parent_crossing P S D.X (.leaf D.a) _ (!D.sa) hs x y hxX hxP hy hyP hyX

theorem source_c_crossing {T S : Tree} (D : LiteralGeometry T S) (P : List Nat)
    (y : Nat) (hcP : D.c ∈ P) (hy : y ∈ leaves S) (hyP : y ∈ P) (hyc : y ≠ D.c) :
    D.w ++ [D.sb] ∈ minimalVertices P S := by
  have hs := source_vc_address D
  have he : VC D.sa D.sc D.a D.c D.X = orient (!D.sc) (.leaf D.c) (AX D.sa D.a D.X) := by
    cases D.sc <;> rfl
  rw [he] at hs
  exact pendant_parent_crossing P S (.leaf D.c) (AX D.sa D.a D.X) _ (!D.sc) hs D.c y
    (by simp [leaves]) hcP hy hyP (by simpa [leaves] using hyc)

theorem rooted_trace_subtree (P : List Nat) (t u : Tree) (p v : RMAF.Vertex)
    (hs : subtree t p = some u) (hm : p ++ v ∈ rootedSpan P t) : v ∈ rootedSpan P u := by
  induction p generalizing t with
  | nil =>
    simp only [subtree,Option.some.injEq] at hs
    subst u; exact hm
  | cons s p ih =>
    cases t with
    | leaf a => simp [subtree] at hs
    | node l r =>
      cases s with
      | false =>
        simp only [List.cons_append,rootedSpan] at hm
        split at hm
        · simp at hm
        · exact ih l hs (by simpa [prependSide] using hm)
      | true =>
        simp only [List.cons_append,rootedSpan] at hm
        split at hm
        · simp at hm
        · exact ih r hs (by simpa [prependSide] using hm)

theorem subtree_vertex (t u : Tree) (p : RMAF.Vertex) (hs : subtree t p = some u) :
    p ∈ vertices t := by
  induction p generalizing t with
  | nil => cases t <;> simp [vertices]
  | cons s p ih =>
    cases t with
    | leaf a => simp [subtree] at hs
    | node l r =>
      cases s with
      | false => have hm := ih l hs; simp [vertices,prependSide,hm]
      | true => have hm := ih r hs; simp [vertices,prependSide,hm]

theorem subtreeLabels_of_subtree (t u : Tree) (p : RMAF.Vertex) (hs : subtree t p = some u) :
    subtreeLabels t p = leaves u := by
  induction p generalizing t with
  | nil => simp only [subtree,Option.some.injEq] at hs; subst u; rfl
  | cons s p ih =>
    cases t with
    | leaf a => simp [subtree] at hs
    | node l r => cases s <;> exact ih _ hs

theorem literal_pendant_arcs_mem {T S : Tree} (D : LiteralGeometry T S) :
    xArc D.w D.sa D.sc D.sb ∈ cuts S D.a D.b ∧ cArc D.w D.sc D.sb ∈ cuts S D.a D.b := by
  have sep := source_label_separation D
  have spine := source_spine D [D.a,D.b] (by simp) (by simp)
  have hxsub := source_x_address D
  have hcsub := source_c_address D
  have hxroot : rootedSpan [D.a,D.b] D.X = [] := rooted_empty_of_disjoint _ _ (by
    intro x hx hp
    simp at hp
    rcases hp with h | h
    · subst x; exact sep.2.2.2.1 hx
    · subst x; exact sep.2.2.2.2.1 hx)
  have hxoff : xArc D.w D.sa D.sc D.sb ∉ minimalVertices [D.a,D.b] S := by
    intro hm
    have ht := rooted_trace_subtree [D.a,D.b] S D.X (xArc D.w D.sa D.sc D.sb) [] hxsub
      (by simpa using minimal_subset_rooted _ _ _ hm)
    simp [hxroot] at ht
  have hcoff : cArc D.w D.sc D.sb ∉ minimalVertices [D.a,D.b] S := by
    intro hm
    exact rooted_leaf_not_mem [D.a,D.b] S _ D.c hcsub (by simp; grind)
      (minimal_subset_rooted _ _ _ hm)
  constructor
  · apply List.mem_filter.mpr
    refine ⟨subtree_vertex S D.X _ hxsub, ?_⟩
    have hd : (xArc D.w D.sa D.sc D.sb).dropLast = D.w ++ [D.sb,D.sc] := by simp [xArc]
    have hne : (xArc D.w D.sa D.sc D.sb).isEmpty = false := by simp [xArc]
    simp [hne,hd,spine.2.2,hxoff]
  · apply List.mem_filter.mpr
    refine ⟨subtree_vertex S (.leaf D.c) _ hcsub, ?_⟩
    have hd : (cArc D.w D.sc D.sb).dropLast = D.w ++ [D.sb] := by simp [cArc]
    have hne : (cArc D.w D.sc D.sb).isEmpty = false := by simp [cArc]
    simp [hne,hd,spine.2.1,hcoff]

theorem two_list_from_members {α : Type} (L : List α) (x y : α)
    (hl : L.length = 2) (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y) :
    L = [x,y] ∨ L = [y,x] := by
  cases L with
  | nil => simp at hl
  | cons z zs =>
    cases zs with
    | nil => simp at hl
    | cons w ws =>
      have he : ws = [] := by simpa using hl
      subst ws
      simp only [List.mem_cons,List.mem_singleton] at hx hy
      grind

theorem literal_cuts_two_orders {T S : Tree} (D : LiteralGeometry T S) :
    cuts S D.a D.b = [xArc D.w D.sa D.sc D.sb,cArc D.w D.sc D.sb] ∨
    cuts S D.a D.b = [cArc D.w D.sc D.sb,xArc D.w D.sa D.sc D.sb] := by
  have hne : xArc D.w D.sa D.sc D.sb ≠ cArc D.w D.sc D.sb := by
    intro he
    have hl := congrArg List.length he
    simp [xArc,cArc] at hl
  exact two_list_from_members _ _ _ D.two (literal_pendant_arcs_mem D).1 (literal_pendant_arcs_mem D).2 hne

#print axioms source_spine
#print axioms source_x_crossing
#print axioms literal_cuts_two_orders
end G0Shared

namespace G0Shared
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.CherryBranching
open G0Resume GenericG0Exchange VertexGeometry

theorem literal_pendant_partition_orders {T S : Tree} (D : LiteralGeometry T S) :
    pendantPartition S D.a D.b = [leaves D.X,[D.c],Universal233.CherryBranching.coreLabels S D.a D.b] ∨
    pendantPartition S D.a D.b = [[D.c],leaves D.X,Universal233.CherryBranching.coreLabels S D.a D.b] := by
  have hx := subtreeLabels_of_subtree S D.X _ (source_x_address D)
  have hc := subtreeLabels_of_leaf S _ D.c (source_c_address D)
  rcases literal_cuts_two_orders D with he | he
  · exact Or.inl (by simp [pendantPartition,he,hx,hc])
  · exact Or.inr (by simp [pendantPartition,he,hx,hc])

theorem literal_core_mem_iff {T S : Tree} (D : LiteralGeometry T S) (x : Nat) :
    x ∈ Universal233.CherryBranching.coreLabels S D.a D.b ↔
      x ∈ leaves S ∧ x ∉ leaves D.X ∧ x ≠ D.c := by
  have hx := subtreeLabels_of_subtree S D.X _ (source_x_address D)
  have hc := subtreeLabels_of_leaf S _ D.c (source_c_address D)
  rcases literal_cuts_two_orders D with he | he
  · simp [Universal233.CherryBranching.coreLabels,he,hx,hc]
  · simp [Universal233.CherryBranching.coreLabels,he,hx,hc]; grind

theorem agreement_shared_refines_pendant {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true)
    (hshared : ∃ P ∈ G, D.a ∈ P ∧ D.b ∈ P) :
    Refines G (pendantPartition S D.a D.b) := by
  obtain ⟨P,hP,haP,hbP⟩ := hshared
  have hag := hg
  simp only [agreement,Bool.and_eq_true] at hag
  have hs := hag.1.1.1.2
  have he := hag.2
  have hrP := List.all_eq_true.mp hag.1.1.2 P hP
  have hPsep := shared_block_excludes_pendants D P haP hbP hrP
  have hspine := source_spine D P haP hbP
  have hcov := partition_flat_coverage (leaves S) G hs
  have hxpart : leaves D.X ∈ pendantPartition S D.a D.b := by
    rcases literal_pendant_partition_orders D with h | h <;> simp [h]
  have hcpart : [D.c] ∈ pendantPartition S D.a D.b := by
    rcases literal_pendant_partition_orders D with h | h <;> simp [h]
  have hcorepart : Universal233.CherryBranching.coreLabels S D.a D.b ∈ pendantPartition S D.a D.b := by
    simp [pendantPartition]
  intro Q hQ
  by_cases hqp : Q = P
  · subst Q
    refine ⟨_,hcorepart,?_⟩
    intro x hx
    exact (literal_core_mem_iff D x).mpr ⟨hcov x (List.mem_flatten.mpr ⟨P,hP,hx⟩),hPsep x hx⟩
  by_cases hxQ : ∃ x ∈ Q, x ∈ leaves D.X
  · obtain ⟨x,hxQ,hxX⟩ := hxQ
    refine ⟨leaves D.X,hxpart,?_⟩
    intro y hyQ
    by_cases hyX : y ∈ leaves D.X
    · exact hyX
    · have hyS := hcov y (List.mem_flatten.mpr ⟨Q,hQ,hyQ⟩)
      have hm := source_x_crossing D Q x y hxX hxQ hyS hyQ hyX
      exact False.elim (pairwise_no_common S G he Q P hQ hP hqp _ hm hspine.2.2)
  by_cases hcQ : D.c ∈ Q
  · refine ⟨[D.c],hcpart,?_⟩
    intro y hyQ
    by_cases hyc : y = D.c
    · simp [hyc]
    · have hyS := hcov y (List.mem_flatten.mpr ⟨Q,hQ,hyQ⟩)
      have hm := source_c_crossing D Q y hcQ hyS hyQ hyc
      exact False.elim (pairwise_no_common S G he Q P hQ hP hqp _ hm hspine.2.1)
  · refine ⟨_,hcorepart,?_⟩
    intro x hx
    apply (literal_core_mem_iff D x).mpr
    refine ⟨hcov x (List.mem_flatten.mpr ⟨Q,hQ,hx⟩),?_,?_⟩
    · intro hxX; exact hxQ ⟨x,hx,hxX⟩
    · intro hxc; subst x; exact hcQ hx

#print axioms literal_pendant_partition_orders
#print axioms agreement_shared_refines_pendant
end G0Shared

namespace G0Shared
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.CherryBranching
open G0Resume GenericG0Exchange VertexGeometry

theorem vertices_nonempty (t : Tree) : vertices t ≠ [] := by cases t <;> simp [vertices]

theorem rooted_all_selected (P : List Nat) (t : Tree) (h : ∀ x ∈ leaves t, x ∈ P) :
    rootedSpan P t = vertices t := by
  induction t with
  | leaf a => simp [rootedSpan,vertices,h a (by simp [leaves])]
  | node l r ihl ihr =>
    have hl := ihl (fun x hx => h x (List.mem_append_left _ hx))
    have hr := ihr (fun x hx => h x (List.mem_append_right _ hx))
    simp [rootedSpan,vertices,hl,hr,vertices_nonempty]

theorem minimal_all_selected (P : List Nat) (t : Tree) (h : ∀ x ∈ leaves t, x ∈ P) :
    minimalVertices P t = vertices t := by
  cases t with
  | leaf a => simp [minimalVertices,vertices,h a (by simp [leaves])]
  | node l r =>
    have hl := rooted_all_selected P l (fun x hx => h x (List.mem_append_left _ hx))
    have hr := rooted_all_selected P r (fun x hx => h x (List.mem_append_right _ hx))
    simp [minimalVertices,hl,hr,vertices,vertices_nonempty]

theorem filter_leaves_subtree (t u : Tree) (p : RMAF.Vertex)
    (hn : (leaves t).Nodup) (hs : subtree t p = some u) :
    (leaves t).filter (leaves u).contains = leaves u := by
  induction p generalizing t with
  | nil =>
    simp only [subtree,Option.some.injEq] at hs
    subst u; exact List.filter_eq_self.mpr (by simp)
  | cons s p ih =>
    cases t with
    | leaf a => simp [subtree] at hs
    | node l r =>
      simp only [leaves,List.nodup_append] at hn
      cases s with
      | false =>
        have hr : (leaves r).filter (leaves u).contains = [] := List.filter_eq_nil_iff.mpr (by
          intro x hxr hxu
          have hxu' := List.contains_iff_mem.mp hxu
          exact hn.2.2 x ((subtree_leaves_sublist l p u hs).subset hxu') x hxr rfl)
        simp only [leaves,List.filter_append,ih l hn.1 hs,hr,List.append_nil]
      | true =>
        have hl : (leaves l).filter (leaves u).contains = [] := List.filter_eq_nil_iff.mpr (by
          intro x hxl hxu
          have hxu' := List.contains_iff_mem.mp hxu
          exact hn.2.2 x hxl x ((subtree_leaves_sublist r p u hs).subset hxu') rfl)
        simp only [leaves,List.filter_append,ih r hn.2.1 hs,hl,List.nil_append]

theorem minimal_subtree_mask (t u : Tree) (p : RMAF.Vertex)
    (hn : (leaves t).Nodup) (hs : subtree t p = some u) :
    minimalVertices (leaves u) t = (vertices u).map (fun v => p ++ v) := by
  induction p generalizing t with
  | nil =>
    simp only [subtree,Option.some.injEq] at hs
    subst u
    simpa using minimal_all_selected (leaves t) t (by simp)
  | cons s p ih =>
    cases t with
    | leaf a => simp [subtree] at hs
    | node l r =>
      simp only [leaves,List.nodup_append] at hn
      obtain ⟨x,hxu⟩ := List.exists_mem_of_ne_nil (leaves u) (leaves_nonempty u)
      cases s with
      | false =>
        have hxr : ∀ y ∈ leaves r, y ∉ leaves u := by
          intro y hyr hyu
          exact hn.2.2 y ((subtree_leaves_sublist l p u hs).subset hyu) y hyr rfl
        have hr := rooted_empty_of_disjoint (leaves u) r hxr
        have hlm := rooted_root_of_selected (leaves u) l x ((subtree_leaves_sublist l p u hs).subset hxu) hxu
        have hln : rootedSpan (leaves u) l ≠ [] := by intro he; simp [he] at hlm
        simp [minimalVertices,hr,hln,ih l hn.1 hs,prependSide,List.map_map]
      | true =>
        have hxl : ∀ y ∈ leaves l, y ∉ leaves u := by
          intro y hyl hyu
          exact hn.2.2 y hyl y ((subtree_leaves_sublist r p u hs).subset hyu) rfl
        have hl := rooted_empty_of_disjoint (leaves u) l hxl
        simp [minimalVertices,hl,ih r hn.2.1 hs,prependSide,List.map_map]

theorem subtree_mask_disjoint (t u : Tree) (p : RMAF.Vertex)
    (hn : (leaves t).Nodup) (hs : subtree t p = some u) (Q : List Nat)
    (hoff : ∀ x ∈ leaves u, x ∉ Q) :
    disjointVertices (minimalVertices (leaves u) t) (minimalVertices Q t) = true := by
  have hmask := minimal_subtree_mask t u p hn hs
  have hroot := rooted_empty_of_disjoint Q u hoff
  apply List.all_eq_true.mpr
  intro v hv
  rw [hmask] at hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  have hnot : p ++ w ∉ minimalVertices Q t := by
    intro hm
    have ht := rooted_trace_subtree Q t u p w hs (minimal_subset_rooted Q t _ hm)
    simp [hroot] at ht
  simp [hnot]

theorem disjointVertices_symm (A B : List RMAF.Vertex) (h : disjointVertices A B = true) :
    disjointVertices B A = true := by
  apply List.all_eq_true.mpr
  intro v hv
  have hnot : v ∉ A := by
    intro ha
    have hf := List.all_eq_true.mp h v ha
    simp [hv] at hf
  simp [hnot]

theorem mask_partition_check (L Y Z : List Nat) (hn : L.Nodup)
    (hy : L.filter Y.contains = Y) (hz : L.filter Z.contains = Z)
    (hdis : ∀ x ∈ Y, x ∉ Z) (hyne : Y ≠ []) (hzne : Z ≠ [])
    (hrne : L.filter (fun x => !((Y++Z).contains x)) ≠ []) :
    partitionCheck L [Y,Z,L.filter (fun x => !((Y++Z).contains x))] = true := by
  let R := L.filter (fun x => !((Y++Z).contains x))
  have hyn : Y.Nodup := by rw [←hy]; exact List.Pairwise.filter _ hn
  have hzn : Z.Nodup := by rw [←hz]; exact List.Pairwise.filter _ hn
  have hrn : R.Nodup := List.Pairwise.filter _ hn
  have hyL : ∀ x ∈ Y, x ∈ L := by
    intro x hx; rw [←hy] at hx; exact (List.mem_filter.mp hx).1
  have hzL : ∀ x ∈ Z, x ∈ L := by
    intro x hx; rw [←hz] at hx; exact (List.mem_filter.mp hx).1
  have hrL : ∀ x ∈ R, x ∈ L ∧ x ∉ Y ∧ x ∉ Z := by
    intro x hx; simp [R] at hx; grind
  have hzr : (Z++R).Nodup := List.nodup_append.mpr ⟨hzn,hrn,by
    intro x hx y hy he; subst y; exact (hrL x hy).2.2 hx⟩
  have hflat : ([Y,Z,R] : List (List Nat)).flatten.Nodup := by
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
    exact List.nodup_append.mpr ⟨hyn,hzr,by
      intro x hx y hy he; subst y
      rcases List.mem_append.mp hy with hy | hy
      · exact hdis x hx hy
      · exact (hrL x hy).2.1 hx⟩
  have hcov : ∀ x, x ∈ ([Y,Z,R] : List (List Nat)).flatten ↔ x ∈ L := by
    intro x
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact hyL x h
      · exact hzL x h
      · exact (hrL x h).1
    · intro hx
      by_cases hY : x ∈ Y
      · exact Or.inl hY
      by_cases hZ : x ∈ Z
      · exact Or.inr (Or.inl hZ)
      · exact Or.inr (Or.inr (by simp [R,hx,hY,hZ]))
  change partitionCheck L [Y,Z,R] = true
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro P hP
    have hRne : R ≠ [] := hrne
    simp at hP
    rcases hP with h | h | h <;> subst P <;> simp [hyne,hzne,hRne]
  · intro x hx; exact beq_iff_eq.mpr (hflat.count_of_mem ((hcov x).mpr hx))
  · intro x hx; exact List.contains_iff_mem.mpr ((hcov x).mp hx)

theorem split_two_masks (L Y Z : List Nat)
    (hy : L.filter Y.contains = Y) (hz : L.filter Z.contains = Z)
    (hdis : ∀ x ∈ Y, x ∉ Z) (hyne : Y ≠ []) (hzne : Z ≠ [])
    (hrne : L.filter (fun x => !((Y++Z).contains x)) ≠ []) :
    BinaryExchange.splitAll (BinaryExchange.splitAll [L] Y.contains) Z.contains =
      [Y,Z,L.filter (fun x => !((Y++Z).contains x))] := by
  let A := L.filter (fun x => !(Y.contains x))
  have hzy : ∀ x ∈ Z, x ∉ Y := by intro x hx hy; exact hdis x hy hx
  have hay : A.filter Z.contains = Z := by
    calc
      A.filter Z.contains = L.filter Z.contains := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro x hx
        by_cases hZ : x ∈ Z
        · simp [hZ,hzy x hZ]
        · simp [hZ]
      _ = Z := hz
  have han : A.filter (fun x => !(Z.contains x)) = L.filter (fun x => !((Y++Z).contains x)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x hx
    by_cases hY : x ∈ Y <;> by_cases hZ : x ∈ Z <;> simp [hY,hZ]
  have hane : A ≠ [] := by
    intro he
    have hz0 : Z = [] := by simpa [he] using hay.symm
    exact hzne hz0
  have hyz : Y.filter Z.contains = [] := List.filter_eq_nil_iff.mpr (by
    intro x hx; simpa using hdis x hx)
  have hyn : Y.filter (fun x => !(Z.contains x)) = Y := List.filter_eq_self.mpr (by
    intro x hx; simp [hdis x hx])
  have hyE : Y.isEmpty = false := List.isEmpty_eq_false_iff.mpr hyne
  have hzE : Z.isEmpty = false := List.isEmpty_eq_false_iff.mpr hzne
  have haE : A.isEmpty = false := List.isEmpty_eq_false_iff.mpr hane
  have hrE : (L.filter (fun x => !((Y++Z).contains x))).isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr hrne
  have first : BinaryExchange.splitAll [L] Y.contains = [Y,A] := by
    simp only [BinaryExchange.splitAll,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      BinaryExchange.split,BinaryExchange.yes,BinaryExchange.no,hy]
    change [Y,A].filter (fun b => !b.isEmpty) = [Y,A]
    simp only [List.filter_cons,List.filter_nil,hyE,haE,Bool.not_false,↓reduceIte]
  have splitY : BinaryExchange.split Y Z.contains = [Y] := by
    simp only [BinaryExchange.split,BinaryExchange.yes,BinaryExchange.no,hyz,hyn]
    simp only [List.filter_cons,List.filter_nil,List.isEmpty_nil,hyE,Bool.not_false,Bool.not_true,↓reduceIte]
    simp
  have splitA : BinaryExchange.split A Z.contains = [Z,L.filter (fun x => !((Y++Z).contains x))] := by
    simp only [BinaryExchange.split,BinaryExchange.yes,BinaryExchange.no,hay,han]
    simp only [List.filter_cons,List.filter_nil,hzE,hrE,Bool.not_false,↓reduceIte]
  rw [first]
  simp only [BinaryExchange.splitAll,List.flatMap_cons,List.flatMap_nil,splitY,splitA,
    List.append_nil,List.singleton_append]

#print axioms subtree_mask_disjoint
#print axioms mask_partition_check
#print axioms split_two_masks
end G0Shared

namespace G0Shared
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.CherryBranching
open Universal233.Rule5Case322 G0Resume GenericG0Exchange VertexGeometry

theorem literal_core_nonempty {T S : Tree} (D : LiteralGeometry T S) :
    Universal233.CherryBranching.coreLabels S D.a D.b ≠ [] := by
  have haS : D.a ∈ leaves S := (D.same D.a).mp
    ((subtree_leaves_sublist T D.qa _ D.leafA).subset (by simp [leaves]))
  have sep := source_label_separation D
  have haR := (literal_core_mem_iff D D.a).mpr ⟨haS,sep.2.2.2.1,sep.2.1⟩
  intro he; simp [he] at haR

theorem literal_hard_embeddings {T S : Tree} (D : LiteralGeometry T S) :
    pairwiseEmbeddings S (pendantPartition S D.a D.b) = true := by
  let R := Universal233.CherryBranching.coreLabels S D.a D.b
  have sep := source_label_separation D
  have hxC : disjointVertices (minimalVertices (leaves D.X) S) (minimalVertices [D.c] S) = true :=
    subtree_mask_disjoint S D.X _ D.properS (source_x_address D) [D.c] (by
      intro x hx hxc
      have he : x = D.c := by simpa using hxc
      subst x; exact sep.2.2.2.2.2 hx)
  have hxR : disjointVertices (minimalVertices (leaves D.X) S) (minimalVertices R S) = true :=
    subtree_mask_disjoint S D.X _ D.properS (source_x_address D) R (by
      intro x hx hxR; exact ((literal_core_mem_iff D x).mp hxR).2.1 hx)
  have hcR : disjointVertices (minimalVertices [D.c] S) (minimalVertices R S) = true :=
    subtree_mask_disjoint S (.leaf D.c) _ D.properS (source_c_address D) R (by
      intro x hx hxR
      have he : x = D.c := by simpa [leaves] using hx
      exact ((literal_core_mem_iff D x).mp hxR).2.2 he)
  have hcX := disjointVertices_symm _ _ hxC
  rcases literal_pendant_partition_orders D with hp | hp
  · rw [hp]
    change pairwiseEmbeddings S [leaves D.X,[D.c],R] = true
    simp [pairwiseEmbeddings,hxC,hxR,hcR]
  · rw [hp]
    change pairwiseEmbeddings S [[D.c],leaves D.X,R] = true
    simp [pairwiseEmbeddings,hcX,hcR,hxR]

theorem literal_hard_partition_and_arc {T S : Tree} (D : LiteralGeometry T S) :
    partitionCheck (leaves S) (pendantPartition S D.a D.b) = true ∧
    arcPartition S (cuts S D.a D.b) = pendantPartition S D.a D.b := by
  have hxsub := source_x_address D
  have hcsub : subtree S (cArc D.w D.sc D.sb) = some (.leaf D.c) := source_c_address D
  have hx := subtreeLabels_of_subtree S D.X _ hxsub
  have hc := subtreeLabels_of_leaf S _ D.c hcsub
  have hxf := filter_leaves_subtree S D.X _ D.properS hxsub
  have hcf : (leaves S).filter [D.c].contains = [D.c] := filter_leaves_subtree S (.leaf D.c) _ D.properS hcsub
  have hxn := leaves_nonempty D.X
  have hcn : ([D.c] : List Nat) ≠ [] := by simp
  have hdis : ∀ x ∈ leaves D.X, x ∉ [D.c] := by
    intro x hx hxc
    have he : x = D.c := by simpa using hxc
    subst x; exact (source_label_separation D).2.2.2.2.2 hx
  have hdis' : ∀ x ∈ ([D.c] : List Nat), x ∉ leaves D.X := by
    intro x hx hxX; exact hdis x hxX hx
  rcases literal_cuts_two_orders D with hcuts | hcuts
  · have hR : Universal233.CherryBranching.coreLabels S D.a D.b =
        (leaves S).filter (fun x => !((leaves D.X ++ [D.c]).contains x)) := by
      simp [Universal233.CherryBranching.coreLabels,hcuts,hx,hc]
    have hrn : (leaves S).filter (fun x => !((leaves D.X ++ [D.c]).contains x)) ≠ [] := by
      rw [←hR]; exact literal_core_nonempty D
    have hp := mask_partition_check (leaves S) (leaves D.X) [D.c] D.properS hxf hcf hdis hxn hcn hrn
    have hs := split_two_masks (leaves S) (leaves D.X) [D.c] hxf hcf hdis hxn hcn hrn
    constructor
    · simpa [pendantPartition,hcuts,hx,hc,hR] using hp
    · simpa only [arcPartition,arcPartitionFrom,splitForest,hcuts,pendantPartition,
        List.map_cons,List.map_nil,List.cons_append,List.nil_append,hx,hc,hR] using hs
  · have hR : Universal233.CherryBranching.coreLabels S D.a D.b =
        (leaves S).filter (fun x => !(([D.c] ++ leaves D.X).contains x)) := by
      simp [Universal233.CherryBranching.coreLabels,hcuts,hx,hc]
    have hrn : (leaves S).filter (fun x => !(([D.c] ++ leaves D.X).contains x)) ≠ [] := by
      rw [←hR]; exact literal_core_nonempty D
    have hp := mask_partition_check (leaves S) [D.c] (leaves D.X) D.properS hcf hxf hdis' hcn hxn hrn
    have hs := split_two_masks (leaves S) [D.c] (leaves D.X) hcf hxf hdis' hcn hxn hrn
    constructor
    · simpa [pendantPartition,hcuts,hx,hc,hR] using hp
    · simpa only [arcPartition,arcPartitionFrom,splitForest,hcuts,pendantPartition,
        List.map_cons,List.map_nil,List.cons_append,List.nil_append,hx,hc,hR] using hs

theorem literal_hard_branch_guard {T S : Tree} (D : LiteralGeometry T S) :
    currentGuard T S (hardBranch S D.a D.b) = true := by
  have hxsub := source_x_address D
  have hcsub : subtree S (cArc D.w D.sc D.sb) = some (.leaf D.c) := source_c_address D
  have hxne : (xArc D.w D.sa D.sc D.sb).isEmpty = false := by simp [xArc]
  have hcne : (cArc D.w D.sc D.sb).isEmpty = false := by simp [cArc]
  have hxy : xArc D.w D.sa D.sc D.sb ≠ cArc D.w D.sc D.sb := by
    intro he; have hl := congrArg List.length he; simp [xArc,cArc] at hl
  have hnd : (cuts S D.a D.b).Nodup := by
    rcases literal_cuts_two_orders D with h | h <;> simp [h,hxy,Ne.symm hxy]
  have hvalid : (cuts S D.a D.b).all (fun q => !q.isEmpty && (subtree S q).isSome) = true := by
    rcases literal_cuts_two_orders D with h | h <;> simp [h,hxne,hcne,hxsub,hcsub]
  have hlen : (pendantPartition S D.a D.b).length = 3 := by
    rcases literal_pendant_partition_orders D with h | h <;> simp [h]
  have hpart := (literal_hard_partition_and_arc D).1
  have harc := (literal_hard_partition_and_arc D).2
  have hemb := literal_hard_embeddings D
  simp [currentGuard,hardBranch,current,paid,hnd,hvalid,hlen,hpart,hemb,harc,D.two]

theorem literal_hard_branch_mem {T S : Tree} (D : LiteralGeometry T S) :
    hardBranch S D.a D.b ∈ guardedPlan D := by
  apply List.mem_filter.mpr
  refine ⟨?_,literal_hard_branch_guard D⟩
  unfold literalPlan rawPlan
  split
  · simp [typeIBranches]
  · split <;> simp [typeIIBranches]

theorem g0_of_shared_component {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true)
    (hshared : ∃ P ∈ G, D.a ∈ P ∧ D.b ∈ P) :
    ∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧
      H.length ≤ G.length ∧ Refines H child.partition := by
  exact ⟨hardBranch S D.a D.b,literal_hard_branch_mem D,G,hg,Nat.le_refl _,
    agreement_shared_refines_pendant D G hg hshared⟩

theorem g0_witness_or_a_singleton {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) :
    (∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧
      H.length ≤ G.length ∧ Refines H child.partition) ∨
    ([D.b] ∉ G ∧ ¬(∃ P ∈ G, D.a ∈ P ∧ D.b ∈ P) ∧ [D.a] ∈ G) := by
  rcases g0_witness_or_two_remaining_cases D G hg with h | ⟨hb,hs⟩ | h
  · exact Or.inl h
  · exact Or.inl (g0_of_shared_component D G hg hs)
  · exact Or.inr h

#print axioms literal_hard_branch_guard
#print axioms literal_hard_branch_mem
#print axioms g0_of_shared_component
#print axioms g0_witness_or_a_singleton
end G0Shared

namespace G0CutExchangePrefix
open RMAF Universal233.CoreGraph Universal233.HardParent
open VertexGeometry GenericG0Exchange G0Resume

-- Named consumer: splitting an original AF along a target branch edge.
-- A block with labels on both sides necessarily occupies the cut address.
theorem crossing_cut_mem (P : List Nat) (t u : Tree) (q : RMAF.Vertex)
    (hsub : subtree t q = some u) (x y : Nat)
    (hxu : x ∈ leaves u) (hxp : x ∈ P)
    (hyt : y ∈ leaves t) (hyp : y ∈ P) (hyu : y ∉ leaves u) :
    q ∈ minimalVertices P t := by
  induction q generalizing t with
  | nil =>
    simp only [subtree, Option.some.injEq] at hsub
    subst u
    exact False.elim (hyu hyt)
  | cons s q ih =>
    cases t with
    | leaf a => simp [subtree] at hsub
    | node l r =>
      cases s with
      | false =>
        by_cases hyl : y ∈ leaves l
        · exact minimal_lift_left P l r q (ih l hsub hyl)
        · have hyr : y ∈ leaves r := (List.mem_append.mp hyt).resolve_left hyl
          have hq := rooted_subtree_root P l u q hsub x hxu hxp
          have hr := rooted_root_of_selected P r y hyr hyp
          have hln : rootedSpan P l ≠ [] := by intro he; simp [he] at hq
          have hrn : rootedSpan P r ≠ [] := by intro he; simp [he] at hr
          simp [minimalVertices, hln, hrn, prependSide, hq]
      | true =>
        by_cases hyr : y ∈ leaves r
        · exact minimal_lift_right P l r q (ih r hsub hyr)
        · have hyl : y ∈ leaves l := (List.mem_append.mp hyt).resolve_right hyr
          have hq := rooted_subtree_root P r u q hsub x hxu hxp
          have hl := rooted_root_of_selected P l y hyl hyp
          have hln : rootedSpan P l ≠ [] := by intro he; simp [he] at hl
          have hrn : rootedSpan P r ≠ [] := by intro he; simp [he] at hq
          simp [minimalVertices, hln, hrn, prependSide, hq]

-- In particular, two distinct valid AF blocks cannot both cross one edge.
theorem distinct_blocks_not_both_cross (t u : Tree) (q : RMAF.Vertex)
    (hsub : subtree t q = some u) (G : List (List Nat))
    (he : pairwiseEmbeddings t G = true) (P Q : List Nat)
    (hP : P ∈ G) (hQ : Q ∈ G) (hne : P ≠ Q)
    (x y z w : Nat)
    (hx : x ∈ leaves u) (hxP : x ∈ P) (hy : y ∈ leaves t)
    (hyP : y ∈ P) (hyn : y ∉ leaves u)
    (hz : z ∈ leaves u) (hzQ : z ∈ Q) (hw : w ∈ leaves t)
    (hwQ : w ∈ Q) (hwn : w ∉ leaves u) : False := by
  exact pairwise_no_common t G he P Q hP hQ hne q
    (crossing_cut_mem P t u q hsub x y hx hxP hy hyP hyn)
    (crossing_cut_mem Q t u q hsub z w hz hzQ hw hwQ hwn)

#print axioms crossing_cut_mem
#print axioms distinct_blocks_not_both_cross
end G0CutExchangePrefix

namespace G0CutExchangePrefix
open RMAF Universal233.CoreGraph Universal233.HardParent
open VertexGeometry GenericG0Exchange G0Resume

def Crosses (P U : List Nat) : Prop :=
  (∃ x ∈ P, x ∈ U) ∧ (∃ y ∈ P, y ∉ U)

theorem split_length_le_two (P U : List Nat) :
    (BinaryExchange.split P U.contains).length ≤ 2 := by
  unfold BinaryExchange.split
  exact List.length_filter_le _ _

theorem split_length_le_one (P U : List Nat) (h : ¬ Crosses P U) :
    (BinaryExchange.split P U.contains).length ≤ 1 := by
  cases hy : BinaryExchange.yes P U.contains with
  | nil => cases hn : BinaryExchange.no P U.contains <;> simp [BinaryExchange.split, hy, hn]
  | cons x xs =>
    cases hn : BinaryExchange.no P U.contains with
    | nil => simp [BinaryExchange.split, hy, hn]
    | cons y ys =>
      have hx : x ∈ P ∧ x ∈ U := by
        have hm : x ∈ BinaryExchange.yes P U.contains := by simp [hy]
        simpa [BinaryExchange.yes, List.contains_iff_mem] using hm
      have hy' : y ∈ P ∧ y ∉ U := by
        have hm : y ∈ BinaryExchange.no P U.contains := by simp [hn]
        simpa [BinaryExchange.no, List.contains_iff_mem] using hm
      exact False.elim (h ⟨⟨x,hx.1,hx.2⟩,⟨y,hy'.1,hy'.2⟩⟩)

theorem splitAll_non_crossing_length (G : List (List Nat)) (U : List Nat)
    (h : ∀ P ∈ G, ¬ Crosses P U) :
    (BinaryExchange.splitAll G U.contains).length ≤ G.length := by
  induction G with
  | nil => simp [BinaryExchange.splitAll]
  | cons P Ps ih =>
    have hp := split_length_le_one P U (h P (by simp))
    have ht := ih (fun Q hQ => h Q (by simp [hQ]))
    simpa [BinaryExchange.splitAll, Nat.add_comm] using Nat.add_le_add hp ht

theorem one_edge_split_adds_at_most_one (t u : Tree) (q : RMAF.Vertex)
    (hsub : subtree t q = some u) (G : List (List Nat))
    (hc : ∀ P ∈ G, ∀ x ∈ P, x ∈ leaves t)
    (he : pairwiseEmbeddings t G = true) :
    (BinaryExchange.splitAll G (leaves u).contains).length ≤ G.length + 1 := by
  induction G with
  | nil => simp [BinaryExchange.splitAll]
  | cons P Ps ih =>
    simp only [pairwiseEmbeddings, Bool.and_eq_true] at he
    have hct : ∀ Q ∈ Ps, ∀ x ∈ Q, x ∈ leaves t :=
      fun Q hQ x hx => hc Q (by simp [hQ]) x hx
    by_cases hp : Crosses P (leaves u)
    · obtain ⟨⟨x,hxP,hxu⟩,⟨y,hyP,hyn⟩⟩ := hp
      have hqP := crossing_cut_mem P t u q hsub x y hxu hxP
        (hc P (by simp) y hyP) hyP hyn
      have hn : ∀ Q ∈ Ps, ¬ Crosses Q (leaves u) := by
        intro Q hQ hcross
        obtain ⟨⟨z,hzQ,hzu⟩,⟨w,hwQ,hwn⟩⟩ := hcross
        have hqQ := crossing_cut_mem Q t u q hsub z w hzu hzQ (hct Q hQ w hwQ) hwQ hwn
        have hd := List.all_eq_true.mp he.1 Q hQ
        have hv := List.all_eq_true.mp hd q hqP
        simpa [disjointVertices, List.contains_iff_mem, hqQ] using hv
      have hl := split_length_le_two P (leaves u)
      have ht := splitAll_non_crossing_length Ps (leaves u) hn
      simp only [BinaryExchange.splitAll, List.flatMap_cons, List.length_append, List.length_cons] at *
      omega
    · have hl := split_length_le_one P (leaves u) hp
      have ht := ih hct he.2
      simp only [BinaryExchange.splitAll, List.flatMap_cons, List.length_append, List.length_cons] at *
      omega

theorem agreement_one_edge_split_length {t s u : Tree} (q : RMAF.Vertex)
    (hsub : subtree t q = some u) (G : List (List Nat)) (hg : agreement t s G = true) :
    (BinaryExchange.splitAll G (leaves u).contains).length ≤ G.length + 1 := by
  have hp : partitionCheck (leaves t) G = true := by
    simp only [agreement, Bool.and_eq_true] at hg
    exact hg.1.1.1.1
  have he : pairwiseEmbeddings t G = true := by
    simp only [agreement, Bool.and_eq_true] at hg
    exact hg.1.2
  exact one_edge_split_adds_at_most_one t u q hsub G
    (fun P hP x hx => partition_flat_coverage _ _ hp x (List.mem_flatten.mpr ⟨P,hP,hx⟩)) he

#print axioms one_edge_split_adds_at_most_one
#print axioms agreement_one_edge_split_length
end G0CutExchangePrefix

namespace G0CutExchangePrefix
open RMAF Universal233.CoreGraph Universal233.HardParent
open VertexGeometry GenericG0Exchange G0Resume Universal233.Rule5Case322

theorem splitAll_identity_of_blocks (G : List (List Nat)) (q : Nat → Bool)
    (h : ∀ P ∈ G, BinaryExchange.split P q = [P]) :
    BinaryExchange.splitAll G q = G := by
  induction G with
  | nil => rfl
  | cons P Ps ih =>
    have hh := h P (by simp)
    have ht := ih (fun Q hQ => h Q (by simp [hQ]))
    simpa [BinaryExchange.splitAll, hh] using congrArg (fun L => P :: L) ht

theorem singleton_component_cut_identity {t s : Tree} (G : List (List Nat)) (a : Nat)
    (hg : agreement t s G = true) (ha : [a] ∈ G) :
    BinaryExchange.splitAll G ([a].contains) = G := by
  have hp : partitionCheck (leaves t) G = true := by
    simp only [agreement, Bool.and_eq_true] at hg
    exact hg.1.1.1.1
  have iso := singleton_block_isolated G a (partition_flat_nodup _ _ hp) ha
  have hpn := hp
  simp only [partitionCheck, Bool.and_eq_true] at hpn
  apply splitAll_identity_of_blocks
  intro P hP
  have hne : P ≠ [] := by
    have hm := List.all_eq_true.mp hpn.1.1 P hP
    intro he; subst P; simp at hm
  by_cases hpa : a ∈ P
  · have he := iso P hP hpa
    subst P
    simp [BinaryExchange.split, BinaryExchange.yes, BinaryExchange.no]
  · have hneq : ∀ x ∈ P, x ≠ a := by intro x hx he; subst x; exact hpa hx
    have hy : BinaryExchange.yes P ([a].contains) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      simp [hneq x hx, Ne.symm (hneq x hx)]
    have hn : BinaryExchange.no P ([a].contains) = P := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [hneq x hx, Ne.symm (hneq x hx)]
    simp [BinaryExchange.split, hy, hn, hne]

theorem subtreeLabels_of_subtree (t u : Tree) (q : RMAF.Vertex)
    (hsub : subtree t q = some u) : subtreeLabels t q = leaves u := by
  induction q generalizing t with
  | nil =>
    simp only [subtree, Option.some.injEq] at hsub
    subst u; rfl
  | cons b q ih =>
    cases t with
    | leaf a => simp [subtree] at hsub
    | node l r => cases b <;> exact ih _ hsub

theorem singleton_then_edge_adds_at_most_one {t s u : Tree}
    (qa q : RMAF.Vertex) (a : Nat) (G : List (List Nat))
    (ha : LeafAt t qa a) (hsub : subtree t q = some u)
    (hg : agreement t s G = true) (hGa : [a] ∈ G) :
    (arcPartitionFrom t [qa,q] G).length ≤ G.length + 1 := by
  simp only [arcPartitionFrom, Universal233.CherryBranching.splitForest]
  rw [subtreeLabels_of_leaf t qa a ha, singleton_component_cut_identity G a hg hGa,
      subtreeLabels_of_subtree t u q hsub]
  exact agreement_one_edge_split_length q hsub G hg

#print axioms singleton_component_cut_identity
#print axioms singleton_then_edge_adds_at_most_one
end G0CutExchangePrefix

namespace G0Singleton
open RMAF Universal233.CoreGraph Universal233.HardParent
open G0Resume G0Shared GenericG0Exchange

def joinOptions : Option Tree → Option Tree → Option Tree
  | none, v => v
  | some u, none => some u
  | some u, some v => some (.node u v)

def optionShape : Option Tree → Option Tree → Bool
  | none, none => true
  | some u, some v => sameShape u v
  | _, _ => false

theorem restrict_node_join (P : List Nat) (l r : Tree) :
    restrict P (.node l r) = joinOptions (restrict P l) (restrict P r) := by
  cases hl : restrict P l <;> cases hr : restrict P r <;> simp [restrict,hl,hr,joinOptions]

theorem optionShape_join (a b c d : Option Tree)
    (ha : optionShape a c = true) (hb : optionShape b d = true) :
    optionShape (joinOptions a b) (joinOptions c d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [optionShape,joinOptions,sameShape]

theorem optionShape_join_swapped (a b c d : Option Tree)
    (ha : optionShape a d = true) (hb : optionShape b c = true) :
    optionShape (joinOptions a b) (joinOptions c d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [optionShape,joinOptions,sameShape]

theorem sameShape_restrict (P : List Nat) (t u : Tree) (hs : sameShape t u = true) :
    optionShape (restrict P t) (restrict P u) = true := by
  induction t generalizing u with
  | leaf a =>
    have hu := sameShape_leaf_eq a u hs
    subst u
    by_cases ha : a ∈ P <;> simp [restrict,optionShape,sameShape,ha]
  | node l r ihl ihr =>
    cases u with
    | leaf a => simp [sameShape] at hs
    | node v w =>
      simp only [sameShape,Bool.or_eq_true,Bool.and_eq_true] at hs
      rw [restrict_node_join,restrict_node_join]
      rcases hs with hs | hs
      · exact optionShape_join _ _ _ _ (ihl v hs.1) (ihr w hs.2)
      · exact optionShape_join_swapped _ _ _ _ (ihl w hs.1) (ihr v hs.2)

theorem bind_join_restrict (P : List Nat) (a b : Option Tree) :
    (joinOptions a b).bind (restrict P) =
      joinOptions (a.bind (restrict P)) (b.bind (restrict P)) := by
  cases a with
  | none => rfl
  | some u =>
    cases b with
    | none =>
      change restrict P u = joinOptions (restrict P u) none
      cases restrict P u <;> rfl
    | some v => exact restrict_node_join P u v

theorem restrict_restrict_of_subset (P Q : List Nat) (t : Tree)
    (hQP : ∀ x ∈ Q, x ∈ P) :
    (restrict P t).bind (restrict Q) = restrict Q t := by
  induction t with
  | leaf a =>
    by_cases hQ : a ∈ Q
    · have hP := hQP a hQ; simp [restrict,hQ,hP]
    · by_cases hP : a ∈ P <;> simp [restrict,hQ,hP]
  | node l r ihl ihr =>
    calc
      (restrict P (.node l r)).bind (restrict Q) =
          joinOptions ((restrict P l).bind (restrict Q)) ((restrict P r).bind (restrict Q)) := by
        rw [restrict_node_join,bind_join_restrict]
      _ = joinOptions (restrict Q l) (restrict Q r) := by rw [ihl,ihr]
      _ = restrict Q (.node l r) := (restrict_node_join Q l r).symm

theorem restrictionAgrees_subset (t s : Tree) (P Q : List Nat)
    (hp : restrictionAgrees t s P = true) (hQP : ∀ x ∈ Q, x ∈ P)
    (hQT : ∀ x ∈ Q, x ∈ leaves t) (hQS : ∀ x ∈ Q, x ∈ leaves s) (hne : Q ≠ []) :
    restrictionAgrees t s Q = true := by
  obtain ⟨x,hxQ⟩ := List.exists_mem_of_ne_nil Q hne
  obtain ⟨v,hv⟩ := restrict_some_of_selected Q t x (hQT x hxQ) hxQ
  obtain ⟨w,hw⟩ := restrict_some_of_selected Q s x (hQS x hxQ) hxQ
  cases ht : restrict P t with
  | none => simp [restrictionAgrees,ht] at hp
  | some a =>
    cases hs : restrict P s with
    | none => simp [restrictionAgrees,ht,hs] at hp
    | some b =>
      have hab : sameShape a b = true := by simpa [restrictionAgrees,ht,hs] using hp
      have htQ := restrict_restrict_of_subset P Q t hQP
      have hsQ := restrict_restrict_of_subset P Q s hQP
      simp only [ht,Option.bind_some] at htQ
      simp only [hs,Option.bind_some] at hsQ
      have hshape := sameShape_restrict Q a b hab
      rw [htQ,hsQ,hv,hw] at hshape
      simpa [restrictionAgrees,hv,hw,optionShape] using hshape

theorem rooted_root_selected (P : List Nat) (t : Tree)
    (h : ([] : RMAF.Vertex) ∈ rootedSpan P t) : ∃ x ∈ leaves t, x ∈ P := by
  by_cases hx : ∃ x ∈ leaves t, x ∈ P
  · exact hx
  · have he := rooted_empty_of_disjoint P t (by intro x hxt hxP; exact hx ⟨x,hxt,hxP⟩)
    simp [he] at h

theorem rooted_mono (P Q : List Nat) (t : Tree) (hPQ : ∀ x ∈ P, x ∈ Q) :
    ∀ v ∈ rootedSpan P t, v ∈ rootedSpan Q t := by
  intro v
  induction v generalizing t with
  | nil =>
    intro hv
    obtain ⟨x,hxt,hxP⟩ := rooted_root_selected P t hv
    exact rooted_root_of_selected Q t x hxt (hPQ x hxP)
  | cons s v ih =>
    intro hv
    cases t with
    | leaf a =>
      by_cases ha : a ∈ P <;> simp [rootedSpan,ha] at hv
    | node l r =>
      cases s with
      | false =>
        have hc := rooted_trace_subtree P (.node l r) l [false] v rfl hv
        exact rooted_lift_left Q l r v (ih l hc)
      | true =>
        have hc := rooted_trace_subtree P (.node l r) r [true] v rfl hv
        exact rooted_lift_right Q l r v (ih r hc)

theorem minimal_mono (P Q : List Nat) (t : Tree) (hPQ : ∀ x ∈ P, x ∈ Q) :
    ∀ v ∈ minimalVertices P t, v ∈ minimalVertices Q t := by
  induction t with
  | leaf a =>
    intro v hv
    have hr := rooted_mono P Q (.leaf a) hPQ v (minimal_subset_rooted P _ v hv)
    simpa [minimalVertices,rootedSpan] using hr
  | node l r ihl ihr =>
    intro v hv
    by_cases hl : rootedSpan P l = []
    · have hm : v ∈ prependSide true (minimalVertices P r) := by simpa [minimalVertices,hl] using hv
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact minimal_lift_right Q l r w (ihr w hw)
    · by_cases hr : rootedSpan P r = []
      · have hm : v ∈ prependSide false (minimalVertices P l) := by simpa [minimalVertices,hl,hr] using hv
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
        exact minimal_lift_left Q l r w (ihl w hw)
      · have hQL : rootedSpan Q l ≠ [] := by
          intro he
          obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil (rootedSpan P l) hl
          have hm := rooted_mono P Q l hPQ w hw
          simp [he] at hm
        have hQR : rootedSpan Q r ≠ [] := by
          intro he
          obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil (rootedSpan P r) hr
          have hm := rooted_mono P Q r hPQ w hw
          simp [he] at hm
        have mL := rooted_mono P Q l hPQ
        have mR := rooted_mono P Q r hPQ
        simp [minimalVertices,hl,hr,hQL,hQR,prependSide,List.mem_map] at hv ⊢
        grind

#print axioms restrictionAgrees_subset
#print axioms minimal_mono
end G0Singleton

namespace G0Singleton
open RMAF Universal233.CoreGraph Universal233.HardParent
open G0Resume G0Shared GenericG0Exchange BinaryExchange

theorem split_member_cases (P : List Nat) (q : Nat → Bool) (Q : List Nat)
    (hQ : Q ∈ split P q) : (Q = yes P q ∨ Q = no P q) ∧ Q ≠ [] := by
  have h := List.mem_filter.mp hQ
  have hc : Q = yes P q ∨ Q = no P q := by simpa using h.1
  refine ⟨hc,?_⟩
  intro he
  subst Q
  simp at h

theorem split_member_subset (P : List Nat) (q : Nat → Bool) (Q : List Nat)
    (hQ : Q ∈ split P q) : ∀ x ∈ Q, x ∈ P := by
  rcases (split_member_cases P q Q hQ).1 with he | he <;> subst Q
  · intro x hx; exact (List.mem_filter.mp hx).1
  · intro x hx; exact (List.mem_filter.mp hx).1

theorem split_flat_count (P : List Nat) (q : Nat → Bool) (x : Nat) :
    (split P q).flatten.count x = P.count x := by
  simp only [split,List.flatten_filter_not_isEmpty,List.flatten_cons,List.flatten_nil,
    List.append_nil,List.count_append,yes,no]
  induction P with
  | nil => simp
  | cons a P ih =>
    cases hqa : q a <;> by_cases hax : a = x <;>
      simp_all [List.filter_cons,List.count_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem splitAll_flat_count (G : List (List Nat)) (q : Nat → Bool) (x : Nat) :
    (splitAll G q).flatten.count x = G.flatten.count x := by
  induction G with
  | nil => rfl
  | cons P Ps ih =>
    simpa only [splitAll,List.flatMap_cons,List.flatten_append,List.count_append,
      split_flat_count,List.flatten_cons] using congrArg (fun n => P.count x + n) ih

theorem partitionCheck_splitAll (L : List Nat) (G : List (List Nat)) (q : Nat → Bool)
    (hp : partitionCheck L G = true) : partitionCheck L (splitAll G q) = true := by
  have h := hp
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true] at h ⊢
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro Q hQ
    obtain ⟨P,hP,hQP⟩ := List.mem_flatMap.mp hQ
    have hn := (split_member_cases P q Q hQP).2
    cases Q with
    | nil => exact False.elim (hn rfl)
    | cons x xs => rfl
  · intro x hx
    rw [splitAll_flat_count]
    exact h.1.2 x hx
  · intro x hx
    have hc : 0 < G.flatten.count x := by
      rw [←splitAll_flat_count G q x]
      exact List.count_pos_iff.mpr hx
    exact h.2 x (List.count_pos_iff.mp hc)

theorem forest_nodup_of_flat (G : List (List Nat)) (hn : G.flatten.Nodup)
    (hne : ∀ P ∈ G, P ≠ []) : G.Nodup := by
  induction G with
  | nil => simp
  | cons P Ps ih =>
    simp only [List.flatten_cons,List.nodup_append] at hn
    apply List.nodup_cons.mpr
    refine ⟨?_,ih hn.2.1 (fun Q hQ => hne Q (by simp [hQ]))⟩
    intro hP
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil P (hne P (by simp))
    exact hn.2.2 x hx x (List.mem_flatten.mpr ⟨P,hP,hx⟩) rfl

theorem pairwiseEmbeddings_of_distinct (t : Tree) (G : List (List Nat)) (hn : G.Nodup)
    (hdis : ∀ P ∈ G, ∀ Q ∈ G, P ≠ Q →
      disjointVertices (minimalVertices P t) (minimalVertices Q t) = true) :
    pairwiseEmbeddings t G = true := by
  induction G with
  | nil => rfl
  | cons P Ps ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [pairwiseEmbeddings,Bool.and_eq_true]
    constructor
    · apply List.all_eq_true.mpr
      intro Q hQ
      have hpq : P ≠ Q := by intro he; subst Q; exact hn'.1 hQ
      exact hdis P (by simp) Q (by simp [hQ]) hpq
    · exact ih hn'.2 (fun Q hQ R hR hqr => hdis Q (by simp [hQ]) R (by simp [hR]) hqr)

theorem subblocks_disjoint (t : Tree) (G : List (List Nat)) (he : pairwiseEmbeddings t G = true)
    (P R Q U : List Nat) (hP : P ∈ G) (hR : R ∈ G) (hne : P ≠ R)
    (hQP : ∀ x ∈ Q, x ∈ P) (hUR : ∀ x ∈ U, x ∈ R) :
    disjointVertices (minimalVertices Q t) (minimalVertices U t) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  have hvP := minimal_mono Q P t hQP v hv
  have hnot : v ∉ minimalVertices U t := by
    intro hu
    exact pairwise_no_common t G he P R hP hR hne v hvP (minimal_mono U R t hUR v hu)
  simp [hnot]

theorem singleton_yes (P : List Nat) (c : Nat) (hn : P.Nodup) :
    yes P [c].contains = if c ∈ P then [c] else [] := by
  have hpred : ([c].contains) = (fun x => x == c) := by funext x; simp [Bool.beq_eq_decide_eq]
  unfold yes
  rw [hpred,List.filter_beq,hn.count]
  by_cases hc : c ∈ P <;> simp [hc]

theorem singleton_split_cases (P Q : List Nat) (c : Nat) (hn : P.Nodup)
    (hQ : Q ∈ split P [c].contains) : Q = [c] ∨ Q = no P [c].contains := by
  have h := split_member_cases P [c].contains Q hQ
  rcases h.1 with hy | hn'
  · subst Q
    by_cases hc : c ∈ P
    · exact Or.inl (by simp [singleton_yes P c hn,hc])
    · exact False.elim (h.2 (by simp [singleton_yes P c hn,hc]))
  · exact Or.inr hn'

theorem splitAll_singleton_member (L : List Nat) (G : List (List Nat)) (c : Nat)
    (hp : partitionCheck L G = true) (hc : c ∈ L) : [c] ∈ splitAll G [c].contains := by
  obtain ⟨P,hP,hcP⟩ := partition_block_exists L G hp c hc
  have hpn := block_nodup G (partition_flat_nodup L G hp) P hP
  apply List.mem_flatMap.mpr
  refine ⟨P,hP,?_⟩
  simp [split,singleton_yes P c hpn,hcP]

#print axioms partitionCheck_splitAll
#print axioms subblocks_disjoint
#print axioms singleton_split_cases
end G0Singleton

namespace G0Singleton
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.Case322Extraction
open G0Resume G0Shared GenericG0Exchange BinaryExchange VertexGeometry

theorem singleton_split_embeddings (t : Tree) (c : Nat) (pc : RMAF.Vertex)
    (hn : (leaves t).Nodup) (hleaf : LeafAt t pc c)
    (G : List (List Nat)) (hp : partitionCheck (leaves t) G = true)
    (he : pairwiseEmbeddings t G = true) :
    pairwiseEmbeddings t (splitAll G [c].contains) = true := by
  let H := splitAll G [c].contains
  have hpH := partitionCheck_splitAll (leaves t) G [c].contains hp
  have hflat := partition_flat_nodup (leaves t) H hpH
  have hnonempty : ∀ Q ∈ H, Q ≠ [] := by
    intro Q hQ
    obtain ⟨P,hP,hQP⟩ := List.mem_flatMap.mp hQ
    exact (split_member_cases P [c].contains Q hQP).2
  apply pairwiseEmbeddings_of_distinct t H (forest_nodup_of_flat H hflat hnonempty)
  intro Q hQ R hR hQR
  by_cases hQc : Q = [c]
  · subst Q
    have hcR : c ∉ R := by
      intro hc
      have hiso := singleton_block_isolated H c hflat hQ R hR hc
      exact hQR hiso.symm
    exact subtree_mask_disjoint t (.leaf c) pc hn hleaf R (by simpa [leaves] using hcR)
  by_cases hRc : R = [c]
  · subst R
    have hcQ : c ∉ Q := by
      intro hc
      have hiso := singleton_block_isolated H c hflat hR Q hQ hc
      exact hQR hiso
    exact disjointVertices_symm _ _ (subtree_mask_disjoint t (.leaf c) pc hn hleaf Q
      (by simpa [leaves] using hcQ))
  obtain ⟨P,hP,hQP⟩ := List.mem_flatMap.mp hQ
  obtain ⟨U,hU,hRU⟩ := List.mem_flatMap.mp hR
  by_cases hPU : P = U
  · subst U
    have hpn := block_nodup G (partition_flat_nodup _ _ hp) P hP
    have hqeq := (singleton_split_cases P Q c hpn hQP).resolve_left hQc
    have hreq := (singleton_split_cases P R c hpn hRU).resolve_left hRc
    exact False.elim (hQR (hqeq.trans hreq.symm))
  · exact subblocks_disjoint t G he P U Q R hP hU hPU
      (split_member_subset P [c].contains Q hQP) (split_member_subset U [c].contains R hRU)

theorem agreement_singleton_split (t s : Tree) (c : Nat) (pt ps : RMAF.Vertex)
    (hnt : (leaves t).Nodup) (hns : (leaves s).Nodup)
    (hct : LeafAt t pt c) (hcs : LeafAt s ps c)
    (G : List (List Nat)) (hg : agreement t s G = true) :
    agreement t s (splitAll G [c].contains) = true := by
  have h := hg
  simp only [agreement,Bool.and_eq_true] at h ⊢
  have hpt := h.1.1.1.1
  have hps := h.1.1.1.2
  have hpT := partitionCheck_splitAll (leaves t) G [c].contains hpt
  have hpS := partitionCheck_splitAll (leaves s) G [c].contains hps
  have heT := singleton_split_embeddings t c pt hnt hct G hpt h.1.2
  have heS := singleton_split_embeddings s c ps hns hcs G hps h.2
  have hr : (splitAll G [c].contains).all (restrictionAgrees t s) = true := by
    apply List.all_eq_true.mpr
    intro Q hQ
    obtain ⟨P,hP,hQP⟩ := List.mem_flatMap.mp hQ
    have hsub := split_member_subset P [c].contains Q hQP
    have hcovt := partition_flat_coverage (leaves t) G hpt
    have hcovs := partition_flat_coverage (leaves s) G hps
    exact restrictionAgrees_subset t s P Q (List.all_eq_true.mp h.1.1.2 P hP) hsub
      (fun x hx => hcovt x (List.mem_flatten.mpr ⟨P,hP,hsub x hx⟩))
      (fun x hx => hcovs x (List.mem_flatten.mpr ⟨P,hP,hsub x hx⟩))
      (split_member_cases P [c].contains Q hQP).2
  exact ⟨⟨⟨⟨hpT,hpS⟩,hr⟩,heT⟩,heS⟩

theorem agreement_singleton_split_with_count (t s : Tree) (c : Nat) (pt ps : RMAF.Vertex)
    (hnt : (leaves t).Nodup) (hns : (leaves s).Nodup)
    (hct : LeafAt t pt c) (hcs : LeafAt s ps c)
    (G : List (List Nat)) (hg : agreement t s G = true) :
    agreement t s (splitAll G [c].contains) = true ∧
    (splitAll G [c].contains).length ≤ G.length + 1 ∧ [c] ∈ splitAll G [c].contains := by
  have hp : partitionCheck (leaves t) G = true := by
    simp only [agreement,Bool.and_eq_true] at hg; exact hg.1.1.1.1
  have hc : c ∈ leaves t := (subtree_leaves_sublist t pt _ hct).subset (by simp [leaves])
  exact ⟨agreement_singleton_split t s c pt ps hnt hns hct hcs G hg,
    G0CutExchangePrefix.agreement_one_edge_split_length pt hct G hg,
    splitAll_singleton_member (leaves t) G c hp hc⟩

theorem other_singleton_survives_split (G : List (List Nat)) (a c : Nat)
    (ha : [a] ∈ G) (hne : a ≠ c) : [a] ∈ splitAll G [c].contains := by
  apply List.mem_flatMap.mpr
  refine ⟨[a],ha,?_⟩
  simp [split,yes,no,hne,Ne.symm hne]

-- Full-field literal c isolation, with actual AF preservation in BOTH trees.
-- The possible +1 component has not yet been repaid by a merge/exchange.
theorem literal_c_isolation {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (ha : [D.a] ∈ G) :
    let H := splitAll G [D.c].contains
    agreement T S H = true ∧ H.length ≤ G.length + 1 ∧ [D.c] ∈ H ∧ [D.a] ∈ H := by
  have h := agreement_singleton_split_with_count T S D.c D.uc (cArc D.w D.sc D.sb)
    D.properT D.properS D.leafC (source_c_address D) G hg
  exact ⟨h.1,h.2.1,h.2.2,other_singleton_survives_split G D.a D.c ha (source_label_separation D).2.1⟩

#print axioms singleton_split_embeddings
#print axioms agreement_singleton_split
#print axioms literal_c_isolation
end G0Singleton

namespace G0Singleton
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.Case322Extraction Universal233.CherryBranching Universal233.Rule5Case322
open G0Resume G0Shared GenericG0Exchange BinaryExchange VertexGeometry

theorem distinct_blocks_label_disjoint (G : List (List Nat)) (hn : G.flatten.Nodup)
    (P Q : List Nat) (hP : P ∈ G) (hQ : Q ∈ G) (hne : P ≠ Q)
    (x : Nat) (hxP : x ∈ P) (hxQ : x ∈ Q) : False := by
  induction G with
  | nil => simp at hP
  | cons R Rs ih =>
    simp only [List.flatten_cons,List.nodup_append] at hn
    simp only [List.mem_cons] at hP hQ
    rcases hP with hP | hP
    · subst P
      have hQ := hQ.resolve_left (Ne.symm hne)
      exact hn.2.2 x hxP x (List.mem_flatten.mpr ⟨Q,hQ,hxQ⟩) rfl
    · rcases hQ with hQ | hQ
      · subst Q
        exact hn.2.2 x hxQ x (List.mem_flatten.mpr ⟨P,hP,hxP⟩) rfl
      · exact ih hn.2.1 hP hQ

theorem source_bottom_labels {T S : Tree} (D : LiteralGeometry T S) (x : Nat) :
    x ∈ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) ↔
      x = D.a ∨ x = D.b ∨ x = D.c ∨ x ∈ leaves D.X := by
  cases D.sa <;> cases D.sc <;> cases D.sb <;>
    simp [bottom,VC,AX,orient,leaves] <;> grind

theorem block_survives_other_singleton_cut (G : List (List Nat)) (B : List Nat) (c : Nat)
    (hB : B ∈ G) (hcB : c ∉ B) (hne : B ≠ []) : B ∈ splitAll G [c].contains := by
  apply List.mem_flatMap.mpr
  refine ⟨B,hB,?_⟩
  have hy : yes B [c].contains = [] := List.filter_eq_nil_iff.mpr (by
    intro x hx; simp; intro he; subst x; exact hcB hx)
  have hn : no B [c].contains = B := List.filter_eq_self.mpr (by
    intro x hx; simp; intro he; subst x; exact hcB hx)
  simp [split,hy,hn,hne]

-- Source confinement after c is isolated, when b's nonsingleton block lies
-- in the literal core. This does not merge a or repay the possible extra block.
theorem core_b_forest_refines_pendant {T S : Tree} (D : LiteralGeometry T S)
    (H : List (List Nat)) (hh : agreement T S H = true)
    (ha : [D.a] ∈ H) (hc : [D.c] ∈ H)
    (B : List Nat) (hB : B ∈ H) (hbB : D.b ∈ B) (hBne : B ≠ [D.b])
    (hBcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    Refines H (pendantPartition S D.a D.b) := by
  have h := hh
  simp only [agreement,Bool.and_eq_true] at h
  have hp := h.1.1.1.2
  have hn := partition_flat_nodup (leaves S) H hp
  have hcov := partition_flat_coverage (leaves S) H hp
  have sep := source_label_separation D
  have haB : D.a ∉ B := by
    intro haB
    have he := singleton_block_isolated H D.a hn ha B hB haB
    have hba : D.b = D.a := by simpa [he] using hbB
    exact sep.1 hba.symm
  obtain ⟨y,hyB,hyb⟩ := (singleton_or_other B D.b (block_nodup H hn B hB) hbB).resolve_left hBne
  have hya : y ≠ D.a := by intro he; subst y; exact haB hyB
  have hyout : y ∉ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) := by
    rw [source_bottom_labels D y]
    simp [hya,hyb,(hBcore y hyB).1,(hBcore y hyB).2]
  have hbin : D.b ∈ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) :=
    (source_bottom_labels D D.b).mpr (Or.inr (Or.inl rfl))
  have hwB : D.w ∈ minimalVertices B S := subtree_root_crossing B S _ D.w D.source D.b y
    hbin hbB (hcov y (List.mem_flatten.mpr ⟨B,hB,hyB⟩)) hyB hyout
  have hxpart : leaves D.X ∈ pendantPartition S D.a D.b := by
    rcases literal_pendant_partition_orders D with he | he <;> simp [he]
  have hcpart : [D.c] ∈ pendantPartition S D.a D.b := by
    rcases literal_pendant_partition_orders D with he | he <;> simp [he]
  have hrpart : Universal233.CherryBranching.coreLabels S D.a D.b ∈ pendantPartition S D.a D.b := by
    simp [pendantPartition]
  intro Q hQ
  by_cases hxQ : ∃ x ∈ Q, x ∈ leaves D.X
  · obtain ⟨x,hxQ,hxX⟩ := hxQ
    refine ⟨leaves D.X,hxpart,?_⟩
    have hQB : Q ≠ B := by intro he; subst Q; exact (hBcore x hxQ).1 hxX
    have hQa : Q ≠ [D.a] := by
      intro he; have hxa : x = D.a := by simpa [he] using hxQ
      subst x; exact sep.2.2.2.1 hxX
    have hQc : Q ≠ [D.c] := by
      intro he; have hxc : x = D.c := by simpa [he] using hxQ
      subst x; exact sep.2.2.2.2.2 hxX
    have hna : D.a ∉ Q := by
      intro hqa; exact hQa (singleton_block_isolated H D.a hn ha Q hQ hqa)
    have hnc : D.c ∉ Q := by
      intro hqc; exact hQc (singleton_block_isolated H D.c hn hc Q hQ hqc)
    have hnb : D.b ∉ Q := by
      intro hqb; exact distinct_blocks_label_disjoint H hn Q B hQ hB hQB D.b hqb hbB
    intro z hzQ
    by_cases hzX : z ∈ leaves D.X
    · exact hzX
    · have hza : z ≠ D.a := by intro he; subst z; exact hna hzQ
      have hzb : z ≠ D.b := by intro he; subst z; exact hnb hzQ
      have hzc : z ≠ D.c := by intro he; subst z; exact hnc hzQ
      have hzout : z ∉ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) := by
        rw [source_bottom_labels D z]; simp [hza,hzb,hzc,hzX]
      have hxin := (source_bottom_labels D x).mpr (Or.inr (Or.inr (Or.inr hxX)))
      have hwQ := subtree_root_crossing Q S _ D.w D.source x z hxin hxQ
        (hcov z (List.mem_flatten.mpr ⟨Q,hQ,hzQ⟩)) hzQ hzout
      exact False.elim (pairwise_no_common S H h.2 Q B hQ hB hQB D.w hwQ hwB)
  by_cases hcQ : D.c ∈ Q
  · refine ⟨[D.c],hcpart,?_⟩
    have he := singleton_block_isolated H D.c hn hc Q hQ hcQ
    intro z hz; simpa [he] using hz
  · refine ⟨_,hrpart,?_⟩
    intro z hz
    apply (literal_core_mem_iff D z).mpr
    refine ⟨hcov z (List.mem_flatten.mpr ⟨Q,hQ,hz⟩),?_,?_⟩
    · intro hzX; exact hxQ ⟨z,hz,hzX⟩
    · intro he; subst z; exact hcQ hz

theorem literal_c_core_prefix {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true)
    (ha : [D.a] ∈ G) (hbnot : [D.b] ∉ G)
    (B : List Nat) (hB : B ∈ G) (hbB : D.b ∈ B)
    (hBcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    let H := splitAll G [D.c].contains
    agreement T S H = true ∧ H.length ≤ G.length + 1 ∧
      Refines H (hardBranch S D.a D.b).partition ∧ hardBranch S D.a D.b ∈ guardedPlan D := by
  have hiso := literal_c_isolation D G hg ha
  have hcB : D.c ∉ B := by intro hc; exact (hBcore D.c hc).2 rfl
  have hBnil : B ≠ [] := by intro he; simp [he] at hbB
  have hB' := block_survives_other_singleton_cut G B D.c hB hcB hBnil
  have hBne : B ≠ [D.b] := by intro he; subst B; exact hbnot hB
  exact ⟨hiso.1,hiso.2.1,
    core_b_forest_refines_pendant D _ hiso.1 hiso.2.2.2 hiso.2.2.1 B hB' hbB hBne hBcore,
    literal_hard_branch_mem D⟩

#print axioms core_b_forest_refines_pendant
#print axioms literal_c_core_prefix
end G0Singleton

namespace G0Singleton
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.CherryBranching Universal233.Rule5Case322 VertexGeometry
open G0Resume G0Shared

-- This is a proved G0 subcase at its exact hypotheses, not the full residual.
theorem g0_of_core_b_and_singleton_c {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true)
    (ha : [D.a] ∈ G) (hc : [D.c] ∈ G) (hbnot : [D.b] ∉ G)
    (B : List Nat) (hB : B ∈ G) (hbB : D.b ∈ B)
    (hBcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    ∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧
      H.length ≤ G.length ∧ Refines H child.partition := by
  have hBne : B ≠ [D.b] := by intro he; subst B; exact hbnot hB
  exact ⟨hardBranch S D.a D.b,literal_hard_branch_mem D,G,hg,Nat.le_refl _,
    core_b_forest_refines_pendant D G hg ha hc B hB hbB hBne hBcore⟩

#print axioms g0_of_core_b_and_singleton_c
end G0Singleton

namespace G0SingletonCoreFixture
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.Case322Extraction Universal233.CherryBranching Universal233.Rule5Case322
open G0Singleton G0Shared VertexGeometry BinaryExchange

def X := Tree.node (.leaf 3) (.leaf 4)
def C := Tree.node (.node (.leaf 0) (.leaf 1)) (.leaf 5)
def T := Tree.node (.node (.leaf 3) C) (.node (.leaf 4) (.leaf 2))
def S := Tree.node (bottom false false false 0 1 2 X) (.leaf 5)

def D : LiteralGeometry T S where
  X := X
  C := C
  w := [false]
  r := [false,true]
  qa := [false,true,false,false]
  ub := [false,true,false,true]
  uc := [true,true]
  sa := false
  sc := false
  sb := false
  a := 0
  b := 1
  c := 2
  properT := by decide
  properS := by decide
  same := by intro x; simp [T,S,C,X,bottom,VC,AX,orient,leaves]; grind
  source := rfl
  cherry := ⟨[false,true,false],Or.inl rfl⟩
  two := by decide
  core := rfl
  coreLabels := by intro x hx; simp [T,C,X,leaves] at hx ⊢; grind
  bC := by decide
  cC := by decide
  leafA := rfl
  leafB := rfl
  leafC := rfl
  frontier := Or.inl (by decide)
  tailR := by decide
  tailC := by decide
  offR := by decide
  offC := by decide

def G0 : List (List Nat) := [[0],[1,5],[2],[3,4]]
def G1 : List (List Nat) := [[0],[1,5],[2,3],[4]]
def K1 : List (List Nat) := [[0,1,5],[2],[3],[4]]
def G2 : List (List Nat) := [[0],[1,2,4],[3],[5]]
def badMerge : List (List Nat) := [[0,1,2,4],[3],[5]]

example : agreement T S G0 = true ∧ [1] ∉ G0 ∧
    (¬ ∃ P ∈ G0, 0 ∈ P ∧ 1 ∈ P) ∧ [0] ∈ G0 := by decide
example : (hardBranch S 0 1).partition = [[3,4],[2],[0,1,5]] ∧
    currentGuard T S (hardBranch S 0 1) = true := by decide
example : ∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧ H.length ≤ G0.length ∧ Refines H child.partition := by
  apply g0_of_core_b_and_singleton_c D G0 (by decide) (by decide) (by decide) (by decide)
    [1,5] (by decide) (by decide)
  intro x hx
  simp at hx
  rcases hx with rfl | rfl <;> decide
example : agreement T S G1 = true ∧ splitAll G1 [2].contains = [[0],[1,5],[2],[3],[4]] ∧
    agreement T S (splitAll G1 [2].contains) = true ∧ (splitAll G1 [2].contains).length = G1.length + 1 := by decide
example : agreement T S K1 = true ∧ K1.length = G1.length := by decide
example : Refines K1 (hardBranch S 0 1).partition := by
  exact agreement_shared_refines_pendant D K1 (by decide) ⟨[0,1,5],by decide,by decide,by decide⟩
example : agreement T S G2 = true ∧ agreement T S badMerge = false := by decide
#eval "CORE_FULL_FIELD_DIAGNOSTIC_PASS 31/31 D fields, exact residual G0 subcase instantiated; +1 c-cut and finite repair checked; unrestricted merge plant caught"
end G0SingletonCoreFixture

namespace G0Singleton
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.Case322Extraction Universal233.CherryBranching Universal233.Rule5Case322
open G0Resume G0Shared GenericG0Exchange BinaryExchange VertexGeometry

-- Concrete candidate only. No AF preservation is assumed or asserted here.
def absorbA (H : List (List Nat)) (a b : Nat) : List (List Nat) :=
  (H.erase [a]).map (fun P => if P.contains b then a::P else P)

theorem absorbA_length (H : List (List Nat)) (a b : Nat) (ha : [a] ∈ H) :
    (absorbA H a b).length + 1 = H.length := by
  have hpos : 0 < H.length := List.length_pos_iff_exists_mem.mpr ⟨[a],ha⟩
  simp only [absorbA,List.length_map,List.length_erase_of_mem ha]
  omega

theorem absorbA_refines_pendant {T S : Tree} (D : LiteralGeometry T S)
    (H : List (List Nat)) (hh : agreement T S H = true)
    (href : Refines H (pendantPartition S D.a D.b))
    (B : List Nat) (hB : B ∈ H) (hbB : D.b ∈ B)
    (hBcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    Refines (absorbA H D.a D.b) (pendantPartition S D.a D.b) := by
  have h := hh
  simp only [agreement,Bool.and_eq_true] at h
  have hn := partition_flat_nodup (leaves S) H h.1.1.1.2
  have hcov := partition_flat_coverage (leaves S) H h.1.1.1.2
  have sep := source_label_separation D
  have haS : D.a ∈ leaves S := (D.same D.a).mp
    ((subtree_leaves_sublist T D.qa _ D.leafA).subset (by simp [leaves]))
  have haR := (literal_core_mem_iff D D.a).mpr ⟨haS,sep.2.2.2.1,sep.2.1⟩
  have hBR : ∀ x ∈ B, x ∈ Universal233.CherryBranching.coreLabels S D.a D.b := by
    intro x hx
    exact (literal_core_mem_iff D x).mpr ⟨hcov x (List.mem_flatten.mpr ⟨B,hB,hx⟩),hBcore x hx⟩
  have hRpart : Universal233.CherryBranching.coreLabels S D.a D.b ∈ pendantPartition S D.a D.b := by
    simp [pendantPartition]
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hP
  have hQH : Q ∈ H := List.erase_sublist.subset hQ
  by_cases hbQ : D.b ∈ Q
  · have hQB : Q = B := by
      by_cases he : Q = B
      · exact he
      · exact False.elim (distinct_blocks_label_disjoint H hn Q B hQH hB he D.b hbQ hbB)
    subst Q
    have hs : ∀ x ∈ D.a::B, x ∈ Universal233.CherryBranching.coreLabels S D.a D.b := by
      intro x hx
      rcases List.mem_cons.mp hx with he | hx
      · subst x; exact haR
      · exact hBR x hx
    simpa [hbB] using
      (⟨_,hRpart,hs⟩ : ∃ R ∈ pendantPartition S D.a D.b, ∀ x ∈ D.a::B, x ∈ R)
  · simpa [hbQ] using href Q hQH

-- Count and literal branch refinement are paid; agreement of K is still OPEN.
theorem literal_core_absorption_count_refinement {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true)
    (ha : [D.a] ∈ G) (hbnot : [D.b] ∉ G)
    (B : List Nat) (hB : B ∈ G) (hbB : D.b ∈ B)
    (hBcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    let H := splitAll G [D.c].contains
    let K := absorbA H D.a D.b
    K.length ≤ G.length ∧ Refines K (hardBranch S D.a D.b).partition ∧
      hardBranch S D.a D.b ∈ guardedPlan D := by
  have hi := literal_c_isolation D G hg ha
  have hp := literal_c_core_prefix D G hg ha hbnot B hB hbB hBcore
  have hcB : D.c ∉ B := by intro hc; exact (hBcore D.c hc).2 rfl
  have hBne : B ≠ [] := by intro he; simp [he] at hbB
  have hBH := block_survives_other_singleton_cut G B D.c hB hcB hBne
  have hl := absorbA_length (splitAll G [D.c].contains) D.a D.b hi.2.2.2
  refine ⟨by omega,?_,hp.2.2.2⟩
  exact absorbA_refines_pendant D _ hi.1 hp.2.2.1 B hBH hbB hBcore

#print axioms absorbA_length
#print axioms absorbA_refines_pendant
#print axioms literal_core_absorption_count_refinement
end G0Singleton

namespace G0SingletonCandidateControls
open RMAF BinaryExchange G0Singleton G0SingletonCoreFixture
example : absorbA (splitAll G1 [2].contains) 0 1 = K1 := by decide
example : absorbA (splitAll G2 [2].contains) 0 1 = [[2],[0,1,4],[3],[5]] ∧
    agreement T S (absorbA (splitAll G2 [2].contains) 0 1) = false := by decide
#eval "ABSORB_CANDIDATE_CONTROLS_PASS core finite repair exact; unrestricted post-cut merge plant rejected"
end G0SingletonCandidateControls

namespace G0CoreAbsorption
open RMAF G0Resume G0Singleton

theorem rooted_union_mem (t : Tree) (P Q : List Nat) :
    ∀ v, v ∈ rootedSpan (P++Q) t ↔ v ∈ rootedSpan P t ∨ v ∈ rootedSpan Q t := by
  induction t with
  | leaf a => simp [rootedSpan,List.contains_append]; grind
  | node l r ihl ihr =>
    have hel : rootedSpan (P++Q) l = [] ↔ rootedSpan P l = [] ∧ rootedSpan Q l = [] := by
      simp only [List.eq_nil_iff_forall_not_mem,ihl]; grind
    have her : rootedSpan (P++Q) r = [] ↔ rootedSpan P r = [] ∧ rootedSpan Q r = [] := by
      simp only [List.eq_nil_iff_forall_not_mem,ihr]; grind
    by_cases hpl : rootedSpan P l = [] <;> by_cases hpr : rootedSpan P r = [] <;>
      by_cases hql : rootedSpan Q l = [] <;> by_cases hqr : rootedSpan Q r = [] <;>
      have hul := hel <;> have hur := her <;>
      simp_all [rootedSpan,prependSide] <;> grind

-- The rooted path down to the shared anchor supplies the part of Q's stem
-- outside its own minimal hull. The second conjunct is the hull-union fact.
theorem anchored_union_cover (t : Tree) (P Q : List Nat) (x : Nat)
    (hx : x ∈ leaves t) (hp : x ∈ P) (hq : x ∈ Q) :
    (∀ v ∈ rootedSpan (P++Q) t, v ∈ rootedSpan P t ∨ v ∈ minimalVertices Q t) ∧
    (∀ v ∈ rootedSpan (P++Q) t, v ∈ rootedSpan Q t ∨ v ∈ minimalVertices P t) ∧
    (∀ v ∈ minimalVertices (P++Q) t,
      v ∈ minimalVertices P t ∨ v ∈ minimalVertices Q t) := by
  induction t with
  | leaf a =>
    have he : x = a := by simpa [leaves] using hx
    subst x
    simp [rootedSpan,minimalVertices,hp,hq]
  | node l r ihl ihr =>
    have hel : rootedSpan (P++Q) l = [] ↔ rootedSpan P l = [] ∧ rootedSpan Q l = [] := by
      simp only [List.eq_nil_iff_forall_not_mem,rooted_union_mem]; grind
    have her : rootedSpan (P++Q) r = [] ↔ rootedSpan P r = [] ∧ rootedSpan Q r = [] := by
      simp only [List.eq_nil_iff_forall_not_mem,rooted_union_mem]; grind
    have hml := minimal_subset_rooted Q l
    have hmr := minimal_subset_rooted Q r
    have hplm := minimal_subset_rooted P l
    have hprm := minimal_subset_rooted P r
    have hul := rooted_union_mem l P Q
    have hur := rooted_union_mem r P Q
    rcases List.mem_append.mp hx with hxl | hxr
    · have ih := ihl hxl
      have hpl : rootedSpan P l ≠ [] := by
        intro he; have hh := rooted_root_of_selected P l x hxl hp; simp [he] at hh
      have hql : rootedSpan Q l ≠ [] := by
        intro he; have hh := rooted_root_of_selected Q l x hxl hq; simp [he] at hh
      have hulne : rootedSpan (P++Q) l ≠ [] := by simp_all
      by_cases hpr : rootedSpan P r = [] <;> by_cases hqr : rootedSpan Q r = [] <;>
        have hurne := her <;>
        simp_all [rootedSpan,minimalVertices,prependSide] <;> grind
    · have ih := ihr hxr
      have hpr : rootedSpan P r ≠ [] := by
        intro he; have hh := rooted_root_of_selected P r x hxr hp; simp [he] at hh
      have hqr : rootedSpan Q r ≠ [] := by
        intro he; have hh := rooted_root_of_selected Q r x hxr hq; simp [he] at hh
      have hurne : rootedSpan (P++Q) r ≠ [] := by simp_all
      by_cases hpl : rootedSpan P l = [] <;> by_cases hql : rootedSpan Q l = [] <;>
        have hulne := hel <;>
        simp_all [rootedSpan,minimalVertices,prependSide] <;> grind

#print axioms rooted_union_mem
#print axioms anchored_union_cover
end G0CoreAbsorption

namespace G0CoreAbsorption
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open G0Resume G0Shared G0Singleton GenericG0Exchange

def expand (a b : Nat) : Tree → Tree
 | .leaf x => if x = b then .node (.leaf a) (.leaf b) else .leaf x
 | .node l r => .node (expand a b l) (expand a b r)

theorem shape_refl (t : Tree) : sameShape t t = true := by
 induction t <;> simp_all [sameShape]

theorem shape_symm (t u : Tree) (h : sameShape t u = true) : sameShape u t = true := by
 induction t generalizing u with
 | leaf a =>
   have he := sameShape_leaf_eq a u h
   subst u; exact shape_refl _
 | node l r ihl ihr =>
   cases u with
   | leaf a => simp [sameShape] at h
   | node v w =>
     simp only [sameShape,Bool.or_eq_true,Bool.and_eq_true] at h ⊢
     rcases h with h | h
     · exact Or.inl ⟨ihl v h.1,ihr w h.2⟩
     · exact Or.inr ⟨ihr v h.2,ihl w h.1⟩

theorem shape_trans (t u v : Tree) (h : sameShape t u = true)
    (k : sameShape u v = true) : sameShape t v = true := by
 induction t generalizing u v with
 | leaf a =>
   have he := sameShape_leaf_eq a u h
   subst u; exact k
 | node l r ihl ihr =>
   cases u with
   | leaf a => simp [sameShape] at h
   | node u₁ u₂ =>
     cases v with
     | leaf a => simp [sameShape] at k
     | node v₁ v₂ =>
       simp only [sameShape,Bool.or_eq_true,Bool.and_eq_true] at h k ⊢
       rcases h with h | h <;> rcases k with k | k
       · exact Or.inl ⟨ihl _ _ h.1 k.1,ihr _ _ h.2 k.2⟩
       · exact Or.inr ⟨ihl _ _ h.1 k.1,ihr _ _ h.2 k.2⟩
       · exact Or.inr ⟨ihl _ _ h.1 k.2,ihr _ _ h.2 k.1⟩
       · exact Or.inl ⟨ihl _ _ h.1 k.2,ihr _ _ h.2 k.1⟩

theorem shape_expand (t u : Tree) (a b : Nat) (h : sameShape t u = true) :
    sameShape (expand a b t) (expand a b u) = true := by
 induction t generalizing u with
 | leaf x =>
   have he := sameShape_leaf_eq x u h
   subst u; exact shape_refl _
 | node l r ihl ihr =>
   cases u with
   | leaf x => simp [sameShape] at h
   | node v w =>
     simp only [sameShape,Bool.or_eq_true,Bool.and_eq_true] at h
     rcases h with h | h
     · have hl := ihl v h.1; have hr := ihr w h.2
       simp [expand,sameShape,hl,hr]
     · have hl := ihl w h.1; have hr := ihr v h.2
       simp [expand,sameShape,hl,hr]

theorem restrict_all_selected (P : List Nat) (t : Tree)
    (h : ∀ x ∈ leaves t, x ∈ P) : restrict P t = some t := by
 induction t with
 | leaf a => simp [restrict,h a (by simp [leaves])]
 | node l r ihl ihr =>
   have hl := ihl (fun x hx => h x (by simp [leaves,hx]))
   have hr := ihr (fun x hx => h x (by simp [leaves,hx]))
   simp [restrict,hl,hr]

theorem expand_absent (t : Tree) (a b : Nat) (h : b ∉ leaves t) : expand a b t = t := by
 induction t with
 | leaf x => simp_all [expand,leaves,Ne.symm]
 | node l r ihl ihr => simp_all [leaves,expand]

-- Deleting a from a proper literal cherry and reattaching it beside b
-- reconstructs the same rooted shape, including all surrounding context.
theorem restore_cherry (t : Tree) (a b : Nat) (P : List Nat)
    (hn : (leaves t).Nodup) (hc : ActualCherry t a b)
    (ha : a ∉ P) (hb : b ∈ P)
    (hall : ∀ x ∈ leaves t, x = a ∨ x ∈ P) :
    ∃ u, restrict P t = some u ∧ sameShape t (expand a b u) = true := by
 induction t with
 | leaf x => exact False.elim (actual_cherry_leaf_false a b x hc)
 | node l r ihl ihr =>
   have hn' := hn
   simp only [leaves,List.nodup_append] at hn'
   rcases (actual_cherry_node_iff l r a b).mp hc with ⟨hl,hr⟩ | ⟨hl,hr⟩ | hl | hr
   · subst l; subst r
     exact ⟨.leaf b,by simp [restrict,ha,hb],by simp [expand,sameShape]⟩
   · subst l; subst r
     exact ⟨.leaf b,by simp [restrict,ha,hb],by simp [expand,sameShape]⟩
   · obtain ⟨u,hu,hs⟩ := ihl hn'.1 hl (fun x hx => hall x (by simp [leaves,hx]))
     have haL := (actual_cherry_labels l a b hl).1
     have hbL := (actual_cherry_labels l a b hl).2
     have haR : a ∉ leaves r := fun hx => hn'.2.2 a haL a hx rfl
     have hbR : b ∉ leaves r := fun hx => hn'.2.2 b hbL b hx rfl
     have hrP := restrict_all_selected P r (by
       intro x hx; exact (hall x (by simp [leaves,hx])).resolve_left (by intro he; subst x; exact haR hx))
     refine ⟨.node u r,by simp [restrict,hu,hrP],?_⟩
     simp [expand,expand_absent r a b hbR,sameShape,hs,shape_refl]
   · obtain ⟨u,hu,hs⟩ := ihr hn'.2.1 hr (fun x hx => hall x (by simp [leaves,hx]))
     have haR := (actual_cherry_labels r a b hr).1
     have hbR := (actual_cherry_labels r a b hr).2
     have haL : a ∉ leaves l := fun hx => hn'.2.2 a hx a haR rfl
     have hbL : b ∉ leaves l := fun hx => hn'.2.2 b hx b hbR rfl
     have hlP := restrict_all_selected P l (by
       intro x hx; exact (hall x (by simp [leaves,hx])).resolve_left (by intro he; subst x; exact haL hx))
     refine ⟨.node l u,by simp [restrict,hlP,hu],?_⟩
     simp [expand,expand_absent l a b hbL,sameShape,hs,shape_refl]

theorem restricted_proper (P : List Nat) (t u : Tree) (hn : (leaves t).Nodup)
    (h : restrict P t = some u) : (leaves u).Nodup := by
 have he := restricted_leaves P t
 simp only [h,optionLeaves] at he
 rw [he]
 exact hn.filter _

theorem cherry_lifts_restriction (P : List Nat) (t u : Tree) (p : RMAF.Vertex)
    (hs : subtree t p = some u) (a b : Nat) (v : Tree)
    (hv : restrict P u = some v) (hc : ActualCherry v a b) :
    ∃ z, restrict P t = some z ∧ ActualCherry z a b := by
 induction p generalizing t with
 | nil =>
   have he : t = u := by simpa [subtree] using hs
   subst u; exact ⟨v,hv,hc⟩
 | cons s p ih =>
   cases t with
   | leaf x => simp [subtree] at hs
   | node l r =>
     cases s with
     | false =>
       obtain ⟨z,hz,hzc⟩ := ih l hs
       cases hr : restrict P r with
       | none => exact ⟨z,by simp [restrict,hz,hr],hzc⟩
       | some w => exact ⟨.node z w,by simp [restrict,hz,hr],
           (actual_cherry_node_iff z w a b).mpr (Or.inr (Or.inr (Or.inl hzc)))⟩
     | true =>
       obtain ⟨z,hz,hzc⟩ := ih r hs
       cases hl : restrict P l with
       | none => exact ⟨z,by simp [restrict,hz,hl],hzc⟩
       | some w => exact ⟨.node w z,by simp [restrict,hz,hl],
           (actual_cherry_node_iff w z a b).mpr (Or.inr (Or.inr (Or.inr hzc)))⟩

#print axioms restore_cherry
#print axioms cherry_lifts_restriction
end G0CoreAbsorption

namespace G0CoreAbsorption
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.Case322Extraction
open G0Resume G0Shared G0Singleton GenericG0Exchange

theorem source_core_cherry {T S : Tree} (D : LiteralGeometry T S) (B : List Nat)
    (ha : D.a ∉ B) (hb : D.b ∈ B)
    (hcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    ∃ v, restrict (D.a::B) S = some v ∧ ActualCherry v D.a D.b := by
  have sep := source_label_separation D
  have hx : restrict (D.a::B) D.X = none := by
    have hn : ∀ x ∈ leaves D.X, x ∉ D.a::B := by
      intro x hx hm
      rcases List.mem_cons.mp hm with he | hm
      · subst x; exact sep.2.2.2.1 hx
      · exact (hcore x hm).1 hx
    cases he : restrict (D.a::B) D.X with
    | none => rfl
    | some z =>
      obtain ⟨x,hxz⟩ := List.exists_mem_of_ne_nil (leaves z) (leaves_nonempty z)
      have hm := (restricted_mem_iff _ _ _ he x).mp hxz
      exact False.elim (hn x hm.1 hm.2)
  have hc : D.c ∉ D.a::B := by
    simp only [List.mem_cons,not_or]
    exact ⟨Ne.symm sep.2.1,fun hm => (hcore D.c hm).2 rfl⟩
  have hb' : D.b ∈ D.a::B := by simp [hb]
  have hbott : restrict (D.a::B) (bottom D.sa D.sc D.sb D.a D.b D.c D.X) =
      some (orient D.sb (.leaf D.a) (.leaf D.b)) := by
    cases hsa : D.sa <;> cases hsc : D.sc <;> cases hsb : D.sb <;>
      simp [bottom,VC,AX,orient,restrict,hsa,hsc,hsb,hx,hc,hb']
  have hch : ActualCherry (orient D.sb (.leaf D.a) (.leaf D.b)) D.a D.b := by
    cases D.sb <;> simp only [orient,↓reduceIte]
    · exact ⟨[],Or.inl rfl⟩
    · exact ⟨[],Or.inr rfl⟩
  exact cherry_lifts_restriction (D.a::B) S _ D.w D.source D.a D.b _ hbott hch

theorem core_merge_shape {T S : Tree} (D : LiteralGeometry T S) (B : List Nat)
    (ha : D.a ∉ B) (hb : D.b ∈ B)
    (hcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c)
    (hshape : restrictionAgrees T S B = true) :
    restrictionAgrees T S (D.a::B) = true := by
  obtain ⟨t,ht,htc⟩ := restrict_preserves_cherry (D.a::B) T D.a D.b
    (by simp) (by simp [hb]) D.cherry
  obtain ⟨s,hs,hsc⟩ := source_core_cherry D B ha hb hcore
  have htn := restricted_proper (D.a::B) T t D.properT ht
  have hsn := restricted_proper (D.a::B) S s D.properS hs
  have hta : ∀ x ∈ leaves t, x = D.a ∨ x ∈ B := by
    intro x hx
    exact List.mem_cons.mp ((restricted_mem_iff _ _ _ ht x).mp hx).2
  have hsa : ∀ x ∈ leaves s, x = D.a ∨ x ∈ B := by
    intro x hx
    exact List.mem_cons.mp ((restricted_mem_iff _ _ _ hs x).mp hx).2
  obtain ⟨u,hu,htu⟩ := restore_cherry t D.a D.b B htn htc ha hb hta
  obtain ⟨v,hv,hsv⟩ := restore_cherry s D.a D.b B hsn hsc ha hb hsa
  have htu' := restrict_restrict_of_subset (D.a::B) B T (by intro x hx; exact List.mem_cons_of_mem _ hx)
  have hsv' := restrict_restrict_of_subset (D.a::B) B S (by intro x hx; exact List.mem_cons_of_mem _ hx)
  simp only [ht,Option.bind_some,hu] at htu'
  simp only [hs,Option.bind_some,hv] at hsv'
  have huv : sameShape u v = true := by
    simpa [restrictionAgrees,←htu',←hsv'] using hshape
  have hex := shape_expand u v D.a D.b huv
  have hts := shape_trans t (expand D.a D.b u) s htu
    (shape_trans _ _ _ hex (shape_symm _ _ hsv))
  simpa [restrictionAgrees,ht,hs] using hts

#print axioms source_core_cherry
#print axioms core_merge_shape
end G0CoreAbsorption

namespace G0CoreAbsorption
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.Case322Extraction Universal233.CherryBranching
open G0Resume G0Shared G0Singleton GenericG0Exchange VertexGeometry

theorem disjoint_subsets (t : Tree) (P Q U V : List Nat)
    (hP : ∀ x ∈ P, x ∈ U) (hQ : ∀ x ∈ Q, x ∈ V)
    (h : disjointVertices (minimalVertices U t) (minimalVertices V t) = true) :
    disjointVertices (minimalVertices P t) (minimalVertices Q t) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  have hu := minimal_mono P U t hP v hv
  have hh := List.all_eq_true.mp h v hu
  have hn : v ∉ minimalVertices V t := by simpa [List.contains_iff_mem] using hh
  have hnot : v ∉ minimalVertices Q t := fun he => hn (minimal_mono Q V t hQ v he)
  simpa [List.contains_iff_mem] using hnot

theorem ab_hull_clear {T S : Tree} (D : LiteralGeometry T S) (Q : List Nat)
    (ha : D.a ∉ Q) (hb : D.b ∉ Q)
    (hpure : ∃ R ∈ pendantPartition S D.a D.b, ∀ x ∈ Q, x ∈ R) :
    disjointVertices (minimalVertices [D.a,D.b] T) (minimalVertices Q T) = true ∧
    disjointVertices (minimalVertices [D.a,D.b] S) (minimalVertices Q S) = true := by
  have sep := source_label_separation D
  constructor
  · obtain ⟨p,hc⟩ := D.cherry
    rcases hc with hc | hc
    · exact subtree_mask_disjoint T (.node (.leaf D.a) (.leaf D.b)) p D.properT hc Q
        (by simpa [leaves] using (show ∀ x ∈ [D.a,D.b], x ∉ Q from by simp_all))
    · have hd := subtree_mask_disjoint T (.node (.leaf D.b) (.leaf D.a)) p D.properT hc Q
        (by simpa [leaves] using (show ∀ x ∈ [D.b,D.a], x ∉ Q from by simp_all))
      exact disjoint_subsets T [D.a,D.b] Q [D.b,D.a] Q (by simp_all) (by simp) hd
  · obtain ⟨R,hR,hQR⟩ := hpure
    have hRcases : R = leaves D.X ∨ R = [D.c] ∨ R = coreLabels S D.a D.b := by
      rcases literal_pendant_partition_orders D with he | he <;>
        simp only [he,List.mem_cons,List.not_mem_nil,or_false] at hR <;> grind
    rcases hRcases with rfl | rfl | rfl
    · have hd := subtree_mask_disjoint S D.X _ D.properS (source_x_address D) [D.a,D.b]
        (by intro x hx hm; simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
            rcases hm with rfl | rfl
            · exact sep.2.2.2.1 hx
            · exact sep.2.2.2.2.1 hx)
      exact disjoint_subsets S [D.a,D.b] Q [D.a,D.b] (leaves D.X)
        (by simp) hQR (disjointVertices_symm _ _ hd)
    · have hd := subtree_mask_disjoint S (.leaf D.c) _ D.properS (source_c_address D) [D.a,D.b]
        (by simpa [leaves] using (show D.c ∉ [D.a,D.b] from by simp [Ne.symm sep.2.1,Ne.symm sep.2.2.1]))
      exact disjoint_subsets S [D.a,D.b] Q [D.a,D.b] [D.c]
        (by simp) hQR (disjointVertices_symm _ _ hd)
    · have hdis : ∀ x ∈ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X), x ∉ Q := by
        intro x hx hxQ
        have hcore := (literal_core_mem_iff D x).mp (hQR x hxQ)
        rcases (source_bottom_labels D x).mp hx with rfl | rfl | rfl | hxX
        · exact ha hxQ
        · exact hb hxQ
        · exact hcore.2.2 rfl
        · exact hcore.2.1 hxX
      have hd := subtree_mask_disjoint S _ D.w D.properS D.source Q hdis
      exact disjoint_subsets S [D.a,D.b] Q _ Q
        (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl
            · exact (source_bottom_labels D D.a).mpr (Or.inl rfl)
            · exact (source_bottom_labels D D.b).mpr (Or.inr (Or.inl rfl)))
        (by simp) hd

theorem add_anchor_disjoint (t : Tree) (P Q : List Nat) (a b : Nat)
    (hb : b ∈ leaves t) (hbP : b ∈ P)
    (hPQ : disjointVertices (minimalVertices P t) (minimalVertices Q t) = true)
    (habQ : disjointVertices (minimalVertices [a,b] t) (minimalVertices Q t) = true) :
    disjointVertices (minimalVertices (a::P) t) (minimalVertices Q t) = true := by
  have hcover := (anchored_union_cover t P [a,b] b hb hbP (by simp)).2.2
  apply List.all_eq_true.mpr
  intro v hv
  have hbig := minimal_mono (a::P) (P++[a,b]) t (by simp; grind) v hv
  rcases hcover v hbig with hp | hab
  · exact List.all_eq_true.mp hPQ v hp
  · exact List.all_eq_true.mp habQ v hab

theorem erase_target_absent (L : List (List Nat)) (hn : L.Nodup) (a : List Nat) :
    a ∉ L.erase a := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : x = a
    · subst x; simpa using hn'.1
    · simpa [List.erase_cons,he,Ne.symm he] using ih hn'.2

theorem pairwise_map_distinct (t : Tree) (L : List (List Nat)) (f : List Nat → List Nat)
    (hn : L.Nodup)
    (hd : ∀ P ∈ L, ∀ Q ∈ L, P ≠ Q →
      disjointVertices (minimalVertices (f P) t) (minimalVertices (f Q) t) = true) :
    pairwiseEmbeddings t (L.map f) = true := by
  induction L with
  | nil => rfl
  | cons P Ps ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [List.map_cons,pairwiseEmbeddings,Bool.and_eq_true]
    constructor
    · apply List.all_eq_true.mpr
      intro U hU
      obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hU
      exact hd P (by simp) Q (by simp [hQ]) (by intro he; subst Q; exact hn'.1 hQ)
    · exact ih hn'.2 (by intro Q hQ U hU; exact hd Q (by simp [hQ]) U (by simp [hU]))

theorem pure_core_absorb_embeddings {T S : Tree} (D : LiteralGeometry T S)
    (H : List (List Nat)) (hh : agreement T S H = true) (ha : [D.a] ∈ H)
    (href : Refines H (pendantPartition S D.a D.b)) :
    pairwiseEmbeddings T (absorbA H D.a D.b) = true ∧
    pairwiseEmbeddings S (absorbA H D.a D.b) = true := by
  have h := hh
  simp only [agreement,Bool.and_eq_true] at h
  have hflat := partition_flat_nodup (leaves T) H h.1.1.1.1
  have hnon : ∀ P ∈ H, P ≠ [] := by
    have hp := h.1.1.1.1
    simp only [partitionCheck,Bool.and_eq_true] at hp
    intro P hP; have hh := List.all_eq_true.mp hp.1.1 P hP
    simpa using hh
  have hn := forest_nodup_of_flat H hflat hnon
  have hne := erase_target_absent H hn [D.a]
  have hmergen : (H.erase [D.a]).Nodup := hn.erase _
  have hbT : D.b ∈ leaves T := (actual_cherry_labels T D.a D.b D.cherry).2
  have hbS : D.b ∈ leaves S := (D.same D.b).mp hbT
  have hdis : ∀ (t : Tree), t = T ∨ t = S → pairwiseEmbeddings t H = true →
      pairwiseEmbeddings t (absorbA H D.a D.b) = true := by
    intro t ht het
    apply pairwise_map_distinct t (H.erase [D.a]) _ hmergen
    intro P hP Q hQ hpq
    have hPH : P ∈ H := List.erase_sublist.subset hP
    have hQH : Q ∈ H := List.erase_sublist.subset hQ
    have haP : D.a ∉ P := by
      intro he; have hp := singleton_block_isolated H D.a hflat ha P hPH he
      subst P; exact hne hP
    have haQ : D.a ∉ Q := by
      intro he; have hq := singleton_block_isolated H D.a hflat ha Q hQH he
      subst Q; exact hne hQ
    have hpqdis : disjointVertices (minimalVertices P t) (minimalVertices Q t) = true := by
      apply List.all_eq_true.mpr; intro v hv
      have hn : v ∉ minimalVertices Q t := by
        intro hq; exact pairwise_no_common t H het P Q hPH hQH hpq v hv hq
      simpa [List.contains_iff_mem] using hn
    by_cases hbP : D.b ∈ P <;> by_cases hbQ : D.b ∈ Q
    · exact False.elim (distinct_blocks_label_disjoint H hflat P Q hPH hQH hpq D.b hbP hbQ)
    · have hc := ab_hull_clear D Q haQ hbQ (href Q hQH)
      rcases ht with ht | ht
      · subst t; simpa [hbP,hbQ] using add_anchor_disjoint T P Q D.a D.b hbT hbP hpqdis hc.1
      · subst t; simpa [hbP,hbQ] using add_anchor_disjoint S P Q D.a D.b hbS hbP hpqdis hc.2
    · have hc := ab_hull_clear D P haP hbP (href P hPH)
      have hqpdis := disjointVertices_symm _ _ hpqdis
      rcases ht with ht | ht
      · subst t
        have hh := add_anchor_disjoint T Q P D.a D.b hbT hbQ hqpdis hc.1
        simpa [hbP,hbQ] using disjointVertices_symm _ _ hh
      · subst t
        have hh := add_anchor_disjoint S Q P D.a D.b hbS hbQ hqpdis hc.2
        simpa [hbP,hbQ] using disjointVertices_symm _ _ hh
    · simpa [hbP,hbQ] using hpqdis
  exact ⟨hdis T (Or.inl rfl) h.1.2,hdis S (Or.inr rfl) h.2⟩

#print axioms ab_hull_clear
#print axioms add_anchor_disjoint
#print axioms pure_core_absorb_embeddings
end G0CoreAbsorption

namespace G0CoreAbsorption
open RMAF G0Resume G0Shared G0Singleton GenericG0Exchange

theorem flatten_erase_count (H : List (List Nat)) (P : List Nat) (hP : P ∈ H) (x : Nat) :
    (H.erase P).flatten.count x + P.count x = H.flatten.count x := by
  induction H with
  | nil => simp at hP
  | cons Q Qs ih =>
    by_cases he : Q = P
    · subst Q; simp [List.count_append,Nat.add_comm]
    · have hp : P ∈ Qs := (List.mem_cons.mp hP).resolve_left (Ne.symm he)
      have hi := ih hp
      simp [List.erase_cons,he,List.count_append]
      omega

theorem map_add_count (L : List (List Nat)) (a b x : Nat) (hn : L.flatten.Nodup) :
    ((L.map (fun P => if b ∈ P then a::P else P)).flatten).count x =
      L.flatten.count x + if b ∈ L.flatten ∧ x = a then 1 else 0 := by
  induction L with
  | nil => simp
  | cons P Ps ih =>
    have hn' := hn
    simp only [List.flatten_cons,List.nodup_append] at hn'
    have hi := ih hn'.2.1
    simp only [List.map_cons,List.flatten_cons,List.count_append,hi]
    by_cases hbP : b ∈ P
    · have hbPs : b ∉ Ps.flatten := fun hm => hn'.2.2 b hbP b hm rfl
      by_cases he : x = a
      · simp [hbP,hbPs,he,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
      · simp [hbP,hbPs,he,Ne.symm he,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
    · simp [hbP,List.count_append,Nat.add_assoc]

theorem flatten_erase_sublist (H : List (List Nat)) (P : List Nat) :
    (H.erase P).flatten.Sublist H.flatten := by
  induction H with
  | nil => simp
  | cons Q Qs ih =>
    by_cases he : Q = P
    · subst Q; simpa using (List.sublist_append_right P Qs.flatten)
    · simpa [List.erase_cons,he] using (List.Sublist.append_left ih Q)

theorem absorbA_flat_count (H : List (List Nat)) (a b : Nat)
    (hn : H.flatten.Nodup) (ha : [a] ∈ H) (hb : b ∈ H.flatten) (hab : a ≠ b) :
    ∀ x, (absorbA H a b).flatten.count x = H.flatten.count x := by
  have hLn : (H.erase [a]).flatten.Nodup := hn.sublist (flatten_erase_sublist H [a])
  have hbc := flatten_erase_count H [a] ha b
  have hbn : b ∈ (H.erase [a]).flatten := by
    have hpos := List.count_pos_iff.mpr hb
    have he : [a].count b = 0 := by simp [List.count_cons,List.count_nil,hab]
    rw [he] at hbc
    apply List.count_pos_iff.mp
    omega
  intro x
  have he := flatten_erase_count H [a] ha x
  have hm := map_add_count (H.erase [a]) a b x hLn
  have hm' : (absorbA H a b).flatten.count x =
      (H.erase [a]).flatten.count x + if x = a then 1 else 0 := by
    simpa [absorbA,hbn] using hm
  have hs : [a].count x = if x = a then 1 else 0 := by
    by_cases hxa : x = a
    · simp [hxa]
    · simp [List.count_nil,hxa,Ne.symm hxa]
  rw [hs] at he
  omega

theorem absorbA_partition (L : List Nat) (H : List (List Nat)) (a b : Nat)
    (hp : partitionCheck L H = true) (hn : H.flatten.Nodup)
    (ha : [a] ∈ H) (hb : b ∈ H.flatten) (hab : a ≠ b) :
    partitionCheck L (absorbA H a b) = true := by
  have hc := absorbA_flat_count H a b hn ha hb hab
  simp only [partitionCheck,Bool.and_eq_true] at hp ⊢
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply List.all_eq_true.mpr
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hP
    have hQH : Q ∈ H := List.erase_sublist.subset hQ
    have hne := List.all_eq_true.mp hp.1.1 Q hQH
    by_cases hbQ : b ∈ Q <;> simp_all
  · apply List.all_eq_true.mpr
    intro x hx
    rw [hc x]
    exact List.all_eq_true.mp hp.1.2 x hx
  · apply List.all_eq_true.mpr
    intro x hx
    have hpos := List.count_pos_iff.mpr hx
    rw [hc x] at hpos
    exact List.all_eq_true.mp hp.2 x (List.count_pos_iff.mp hpos)

#print axioms absorbA_flat_count
#print axioms absorbA_partition
end G0CoreAbsorption

namespace G0CoreAbsorption
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.Case322Extraction Universal233.CherryBranching
open Universal233.Rule5Case322
open G0Resume G0Shared G0Singleton GenericG0Exchange VertexGeometry BinaryExchange

theorem pure_b_block_core {T S : Tree} (D : LiteralGeometry T S) (P : List Nat)
    (hb : D.b ∈ P) (hpure : ∃ R ∈ pendantPartition S D.a D.b, ∀ x ∈ P, x ∈ R) :
    ∀ x ∈ P, x ∉ leaves D.X ∧ x ≠ D.c := by
  obtain ⟨R,hR,hPR⟩ := hpure
  have sep := source_label_separation D
  have hbc := hPR D.b hb
  have hRcases : R = leaves D.X ∨ R = [D.c] ∨ R = coreLabels S D.a D.b := by
    rcases literal_pendant_partition_orders D with he | he <;>
      simp only [he,List.mem_cons,List.not_mem_nil,or_false] at hR <;> grind
  rcases hRcases with rfl | rfl | rfl
  · exact False.elim (sep.2.2.2.2.1 hbc)
  · have he : D.b = D.c := by simpa using hbc
    exact False.elim (sep.2.2.1 he)
  · intro x hx
    exact ((literal_core_mem_iff D x).mp (hPR x hx)).2

-- The pure-cell merge is an actual original-input AF. Its hypotheses are
-- separately proved for the literal c-isolated core-B candidate below.
theorem pure_core_absorb_agreement {T S : Tree} (D : LiteralGeometry T S)
    (H : List (List Nat)) (hh : agreement T S H = true) (ha : [D.a] ∈ H)
    (href : Refines H (pendantPartition S D.a D.b)) :
    agreement T S (absorbA H D.a D.b) = true := by
  have h := hh
  simp only [agreement,Bool.and_eq_true] at h ⊢
  have hn := partition_flat_nodup (leaves T) H h.1.1.1.1
  have hnon : ∀ P ∈ H, P ≠ [] := by
    have hp := h.1.1.1.1
    simp only [partitionCheck,Bool.and_eq_true] at hp
    intro P hP; have he := List.all_eq_true.mp hp.1.1 P hP
    simpa using he
  have hHn := forest_nodup_of_flat H hn hnon
  have hne := erase_target_absent H hHn [D.a]
  have hbT := (actual_cherry_labels T D.a D.b D.cherry).2
  obtain ⟨B,hB,hbB⟩ := partition_block_exists (leaves T) H h.1.1.1.1 D.b hbT
  have hbf : D.b ∈ H.flatten := List.mem_flatten.mpr ⟨B,hB,hbB⟩
  have hab := (source_label_separation D).1
  have hpT := absorbA_partition (leaves T) H D.a D.b h.1.1.1.1 hn ha hbf hab
  have hpS := absorbA_partition (leaves S) H D.a D.b h.1.1.1.2 hn ha hbf hab
  have he := pure_core_absorb_embeddings D H hh ha href
  refine ⟨⟨⟨⟨hpT,hpS⟩,?_⟩,he.1⟩,he.2⟩
  apply List.all_eq_true.mpr
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hP
  have hQH : Q ∈ H := List.erase_sublist.subset hQ
  have hshape := List.all_eq_true.mp h.1.1.2 Q hQH
  by_cases hbQ : D.b ∈ Q
  · have haQ : D.a ∉ Q := by
      intro hm
      have he := singleton_block_isolated H D.a hn ha Q hQH hm
      subst Q; exact hne hQ
    have hc := pure_b_block_core D Q hbQ (href Q hQH)
    simpa [hbQ] using core_merge_shape D Q haQ hbQ hc hshape
  · simpa [hbQ] using hshape

-- Closes CORE-ABSORPTION-GAP-v1; in fact c need not fail to be singleton.
theorem literal_core_absorption_agreement {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true)
    (ha : [D.a] ∈ G) (hbnot : [D.b] ∉ G)
    (B : List Nat) (hB : B ∈ G) (hbB : D.b ∈ B)
    (hBcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    agreement T S (absorbA (splitAll G [D.c].contains) D.a D.b) = true := by
  have hi := literal_c_isolation D G hg ha
  have hp := literal_c_core_prefix D G hg ha hbnot B hB hbB hBcore
  exact pure_core_absorb_agreement D _ hi.1 hi.2.2.2 hp.2.2.1

theorem core_absorption_gap_v1 (T S : Tree) (D : LiteralGeometry T S)
    (G : List (List Nat)) (B : List Nat)
    (hg : agreement T S G = true) (ha : [D.a] ∈ G)
    (hbnot : [D.b] ∉ G) (_hcnot : [D.c] ∉ G)
    (hB : B ∈ G) (hbB : D.b ∈ B)
    (hBcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    agreement T S (absorbA (splitAll G [D.c].contains) D.a D.b) = true :=
  literal_core_absorption_agreement D G hg ha hbnot B hB hbB hBcore

theorem g0_of_core_b_singleton_a {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true)
    (ha : [D.a] ∈ G) (hbnot : [D.b] ∉ G)
    (B : List Nat) (hB : B ∈ G) (hbB : D.b ∈ B)
    (hBcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    ∃ child ∈ guardedPlan D, ∃ H,
      agreement T S H = true ∧ H.length ≤ G.length ∧ Refines H child.partition := by
  have hf := literal_core_absorption_agreement D G hg ha hbnot B hB hbB hBcore
  have hp := literal_core_absorption_count_refinement D G hg ha hbnot B hB hbB hBcore
  exact ⟨hardBranch S D.a D.b,hp.2.2,absorbA (splitAll G [D.c].contains) D.a D.b,
    hf,hp.1,hp.2.1⟩

theorem g0_of_core_b_with_a_singleton {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (ha : [D.a] ∈ G)
    (B : List Nat) (hB : B ∈ G) (hbB : D.b ∈ B)
    (hBcore : ∀ x ∈ B, x ∉ leaves D.X ∧ x ≠ D.c) :
    ∃ child ∈ guardedPlan D, ∃ H,
      agreement T S H = true ∧ H.length ≤ G.length ∧ Refines H child.partition := by
  by_cases hb : [D.b] ∈ G
  · exact g0_of_b_singleton D G hg hb
  · exact g0_of_core_b_singleton_a D G hg ha hb B hB hbB hBcore

#print axioms pure_core_absorb_agreement
#print axioms literal_core_absorption_agreement
#print axioms core_absorption_gap_v1
#print axioms g0_of_core_b_singleton_a
#print axioms g0_of_core_b_with_a_singleton
end G0CoreAbsorption

namespace G0CoreAbsorptionConsumer
open RMAF G0SingletonCoreFixture G0CoreAbsorption BinaryExchange VertexGeometry
open Universal233.Case322PaidGuard
-- The sealed full31 fixture has c mixed with X; this uses the proved generic
-- consumer, rather than deciding the desired merged conclusion.
example : agreement T S (G0Singleton.absorbA (splitAll G1 [2].contains) 0 1) = true := by
  exact literal_core_absorption_agreement D G1 (by decide) (by decide) (by decide)
    [1,5] (by decide) (by decide) (by decide)
example : ∃ child ∈ guardedPlan D, ∃ H,
    agreement T S H = true ∧ H.length ≤ G1.length ∧ Refines H child.partition := by
  exact g0_of_core_b_with_a_singleton D G1 (by decide) (by decide)
    [1,5] (by decide) (by decide) (by decide)
#eval "CORE_ABSORPTION_CONSUMER_PASS exact gap and core-B G0 instantiated at full31 c-mixed fixture"
end G0CoreAbsorptionConsumer

namespace RootRestrictionHeredity
open RMAF

def optionSame : Option Tree → Option Tree → Bool
  | none, none => true
  | some t, some u => sameShape t u
  | _, _ => false

theorem sameShape_restrict (t u : Tree) (P : List Nat)
    (h : sameShape t u = true) :
    optionSame (restrict P t) (restrict P u) = true := by
  induction t generalizing u with
  | leaf a =>
    cases u with
    | leaf b =>
      have hab : a = b := beq_iff_eq.mp h
      subst b
      by_cases ha : a ∈ P <;> simp [restrict,optionSame,sameShape,ha]
    | node v w => simp [sameShape] at h
  | node l r ihl ihr =>
    cases u with
    | leaf b => simp [sameShape] at h
    | node v w =>
      simp only [sameShape,Bool.or_eq_true,Bool.and_eq_true] at h
      rcases h with h | h
      · have hl := ihl v h.1
        have hr := ihr w h.2
        cases el : restrict P l <;> cases er : restrict P r <;>
          cases ev : restrict P v <;> cases ew : restrict P w <;>
          simp_all [restrict,optionSame,sameShape]
      · have hl := ihl w h.1
        have hr := ihr v h.2
        cases el : restrict P l <;> cases er : restrict P r <;>
          cases ev : restrict P v <;> cases ew : restrict P w <;>
          simp_all [restrict,optionSame,sameShape]

theorem sameShape_further_restriction (t u t' u' : Tree) (P : List Nat)
    (h : sameShape t u = true)
    (ht : restrict P t = some t') (hu : restrict P u = some u') :
    sameShape t' u' = true := by
  have hc := sameShape_restrict t u P h
  simpa only [ht,hu,optionSame] using hc

def restrictOption (P : List Nat) : Option Tree → Option Tree
  | none => none
  | some t => restrict P t

theorem restrict_subset_compose (t : Tree) (P Q : List Nat)
    (hsub : ∀ x, x ∈ Q → x ∈ P) :
    restrictOption Q (restrict P t) = restrict Q t := by
  induction t with
  | leaf a =>
    by_cases hq : a ∈ Q
    · have hp := hsub a hq
      simp [restrict,restrictOption,hp,hq]
    · by_cases hp : a ∈ P <;> simp [restrict,restrictOption,hp,hq]
  | node l r ihl ihr =>
    cases el : restrict P l <;> cases er : restrict P r <;>
      cases eql : restrict Q l <;> cases eqr : restrict Q r <;>
      simp_all [restrict,restrictOption]

theorem restrict_some_of_member (t : Tree) (P : List Nat) (x : Nat)
    (hx : x ∈ leaves t) (hp : x ∈ P) : ∃ u, restrict P t = some u := by
  induction t with
  | leaf a =>
    have hxa : x = a := by simpa [leaves] using hx
    subst x
    exact ⟨.leaf a,by simp [restrict,hp]⟩
  | node l r ihl ihr =>
    have hm : x ∈ leaves l ∨ x ∈ leaves r := by simpa [leaves] using hx
    rcases hm with hl | hr
    · obtain ⟨v,hv⟩ := ihl hl
      cases hw : restrict P r with
      | none => exact ⟨v,by simp [restrict,hv,hw]⟩
      | some w => exact ⟨.node v w,by simp [restrict,hv,hw]⟩
    · obtain ⟨w,hw⟩ := ihr hr
      cases hv : restrict P l with
      | none => exact ⟨w,by simp [restrict,hv,hw]⟩
      | some v => exact ⟨.node v w,by simp [restrict,hv,hw]⟩

theorem restrictionAgrees_subset (t u : Tree) (P Q : List Nat)
    (h : restrictionAgrees t u P = true)
    (hsub : ∀ x, x ∈ Q → x ∈ P)
    (hselected : ∃ x ∈ Q, x ∈ leaves t) :
    restrictionAgrees t u Q = true := by
  cases ht : restrict P t with
  | none => simp [restrictionAgrees,ht] at h
  | some t' =>
    cases hu : restrict P u with
    | none => simp [restrictionAgrees,ht,hu] at h
    | some u' =>
      have hs : sameShape t' u' = true := by
        simpa only [restrictionAgrees,ht,hu] using h
      have hc := sameShape_restrict t' u' Q hs
      have hct := restrict_subset_compose t P Q hsub
      have hcu := restrict_subset_compose u P Q hsub
      simp only [ht,restrictOption] at hct
      simp only [hu,restrictOption] at hcu
      obtain ⟨x,hxq,hxt⟩ := hselected
      obtain ⟨v,hv⟩ := restrict_some_of_member t Q x hxt hxq
      rw [hct,hcu,hv] at hc
      cases hw : restrict Q u with
      | none => simp [hw,optionSame] at hc
      | some w => simpa only [restrictionAgrees,hv,hw,optionSame] using hc

#print axioms sameShape_restrict
#print axioms sameShape_further_restriction
#print axioms restrict_subset_compose
#print axioms restrict_some_of_member
#print axioms restrictionAgrees_subset
end RootRestrictionHeredity

namespace RootSpanMonotonicity
open RMAF

theorem rootedSpan_mono (t : Tree) (P Q : List Nat)
    (hsub : ∀ x, x ∈ Q → x ∈ P) :
    ∀ v, v ∈ rootedSpan Q t → v ∈ rootedSpan P t := by
  induction t with
  | leaf a =>
    by_cases hq : a ∈ Q
    · have hp := hsub a hq
      simp [rootedSpan,hp,hq]
    · simp [rootedSpan,hq]
  | node l r ihl ihr =>
    cases hpl : rootedSpan P l <;> cases hpr : rootedSpan P r <;>
      cases hql : rootedSpan Q l <;> cases hqr : rootedSpan Q r <;>
      simp_all [rootedSpan,prependSide] <;> grind

theorem minimalVertices_mono (t : Tree) (P Q : List Nat)
    (hsub : ∀ x, x ∈ Q → x ∈ P) :
    ∀ v, v ∈ minimalVertices Q t → v ∈ minimalVertices P t := by
  induction t with
  | leaf a =>
    by_cases hq : a ∈ Q
    · have hp := hsub a hq
      simp [minimalVertices,hp,hq]
    · simp [minimalVertices,hq]
  | node l r ihl ihr =>
    have hl := rootedSpan_mono l P Q hsub
    have hr := rootedSpan_mono r P Q hsub
    have hml := G0Resume.minimal_subset_rooted Q l
    have hmr := G0Resume.minimal_subset_rooted Q r
    cases hpl : rootedSpan P l <;> cases hpr : rootedSpan P r <;>
      cases hql : rootedSpan Q l <;> cases hqr : rootedSpan Q r <;>
      simp_all [minimalVertices,prependSide] <;> grind

theorem subblocks_no_common (t : Tree) (P Q P' Q' : List Nat)
    (hp : ∀ x, x ∈ P' → x ∈ P) (hq : ∀ x, x ∈ Q' → x ∈ Q)
    (hd : disjointVertices (minimalVertices P t) (minimalVertices Q t) = true) :
    ∀ v, v ∈ minimalVertices P' t → v ∉ minimalVertices Q' t := by
  intro v hvp hvq
  have hpold := minimalVertices_mono t P P' hp v hvp
  have hqold := minimalVertices_mono t Q Q' hq v hvq
  have hall := List.all_eq_true.mp hd v hpold
  simpa [List.contains_iff_mem,hqold] using hall

#print axioms rootedSpan_mono
#print axioms minimalVertices_mono
#print axioms subblocks_no_common
end RootSpanMonotonicity

namespace RootRestrictionLocality
open RMAF Universal233.CoreGraph GenericG0Exchange

theorem restrict_none_of_disjoint (t : Tree) (P : List Nat)
    (h : ∀ x, x ∈ leaves t → x ∉ P) : restrict P t = none := by
  induction t with
  | leaf a =>
    have ha := h a (by simp [leaves])
    simp [restrict,ha]
  | node l r ihl ihr =>
    have hl := ihl (fun x hx => h x (by simp [leaves,hx]))
    have hr := ihr (fun x hx => h x (by simp [leaves,hx]))
    simp [restrict,hl,hr]

theorem restrict_subtree_closed (t u : Tree) (p : RMAF.Vertex) (P : List Nat)
    (hn : (leaves t).Nodup) (hs : subtree t p = some u)
    (hsel : ∀ x, x ∈ P → x ∈ leaves u) : restrict P t = restrict P u := by
  induction p generalizing t with
  | nil =>
    have he : t = u := by simpa [subtree] using hs
    subst u
    rfl
  | cons s p ih =>
    cases t with
    | leaf a => simp [subtree] at hs
    | node l r =>
      simp only [leaves,List.nodup_append] at hn
      cases s with
      | false =>
        have hno : ∀ x, x ∈ leaves r → x ∉ P := by
          intro x hxr hxp
          have hxl := (subtree_leaves_sublist l p u hs).subset (hsel x hxp)
          exact hn.2.2 x hxl x hxr rfl
        have hr := restrict_none_of_disjoint r P hno
        have he := ih l hn.1 hs
        cases hl : restrict P l <;> simpa [restrict,hl,hr] using he
      | true =>
        have hno : ∀ x, x ∈ leaves l → x ∉ P := by
          intro x hxl hxp
          have hxr := (subtree_leaves_sublist r p u hs).subset (hsel x hxp)
          exact hn.2.2 x hxl x hxr rfl
        have hl := restrict_none_of_disjoint l P hno
        have he := ih r hn.2.1 hs
        cases hr : restrict P r <;> simpa [restrict,hl,hr] using he

#print axioms restrict_none_of_disjoint
#print axioms restrict_subtree_closed
end RootRestrictionLocality

namespace OriginalEdgeClipping
open RMAF

structure HullState where
  a : Bool
  b : Bool
  ab : Bool
  ba : Bool
  mm : Bool
  deriving DecidableEq, Repr

def zero : HullState := ⟨false,false,false,false,false⟩
def join (l r : HullState) : HullState :=
 let ac := l.a && r.a
 let bc := l.b && r.b
 ⟨l.a || r.a, l.b || r.b,
  if bc then l.a || r.a else l.ab || r.ab,
  if ac then l.b || r.b else l.ba || r.ba,
  if ac && bc then true else if ac then l.ab || r.ab else if bc then l.ba || r.ba else l.mm || r.mm⟩

def hullState (A B : List Nat) : Tree → HullState
 | .leaf x => let a := A.contains x; let b := B.contains x; ⟨a,b,a&&b,a&&b,a&&b⟩
 | .node l r => join (hullState A B l) (hullState A B r)

theorem join_zero_left (s : HullState) : join zero s = s := by cases s; simp [join,zero]
theorem join_zero_right (s : HullState) : join s zero = s := by cases s; simp [join,zero]
theorem join_comm (l r : HullState) : join l r = join r l := by
 cases l; cases r; simp [join,Bool.or_comm,Bool.and_comm]

def Overlap (V W : List RMAF.Vertex) : Prop := ∃ v, v ∈ V ∧ v ∈ W

theorem overlap_comm (V W : List RMAF.Vertex) : Overlap V W ↔ Overlap W V := by
 simp only [Overlap]; constructor <;> rintro ⟨v,hv,hw⟩ <;> exact ⟨v,hw,hv⟩

@[simp] theorem overlap_nil_left (W : List RMAF.Vertex) : ¬ Overlap [] W := by simp [Overlap]
@[simp] theorem overlap_nil_right (W : List RMAF.Vertex) : ¬ Overlap W [] := by simp [Overlap]
@[simp] theorem overlap_append_left (U V W : List RMAF.Vertex) :
 Overlap (U++V) W ↔ Overlap U W ∨ Overlap V W := by simp [Overlap] <;> grind
@[simp] theorem overlap_append_right (U V W : List RMAF.Vertex) :
 Overlap U (V++W) ↔ Overlap U V ∨ Overlap U W := by simp [Overlap] <;> grind
@[simp] theorem overlap_prepend (s : Bool) (V W : List RMAF.Vertex) :
 Overlap (prependSide s V) (prependSide s W) ↔ Overlap V W := by simp [Overlap,prependSide] <;> grind
@[simp] theorem overlap_prepend_ne (s t : Bool) (V W : List RMAF.Vertex) (hne : s ≠ t) :
 ¬ Overlap (prependSide s V) (prependSide t W) := by simp [Overlap,prependSide] <;> grind
@[simp] theorem overlap_root_prepend (s : Bool) (W : List RMAF.Vertex) :
 ¬ Overlap [[]] (prependSide s W) := by simp [Overlap,prependSide]
@[simp] theorem overlap_prepend_root (s : Bool) (W : List RMAF.Vertex) :
 ¬ Overlap (prependSide s W) [[]] := by simp [Overlap,prependSide]
@[simp] theorem overlap_cons_left (v : RMAF.Vertex) (V W : List RMAF.Vertex) :
 Overlap (v::V) W ↔ v ∈ W ∨ Overlap V W := by simp [Overlap] <;> grind
@[simp] theorem overlap_cons_right (v : RMAF.Vertex) (V W : List RMAF.Vertex) :
 Overlap V (v::W) ↔ v ∈ V ∨ Overlap V W := by simp [Overlap] <;> grind
@[simp] theorem root_not_prepend (s : Bool) (V : List RMAF.Vertex) :
 ([] : RMAF.Vertex) ∉ prependSide s V := by simp [prependSide]
@[simp] theorem overlap_root_root : Overlap [[]] [[]] := by simp [Overlap]

theorem minimal_empty_of_rooted_empty (P : List Nat) (t : Tree) (h : rootedSpan P t = []) :
 minimalVertices P t = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro v hv
 have := G0Resume.minimal_subset_rooted P t v hv
 simp [h] at this

theorem rooted_root_of_nonempty (P : List Nat) (t : Tree) (h : rootedSpan P t ≠ []) :
 ([] : RMAF.Vertex) ∈ rootedSpan P t := by
 cases t with
 | leaf x => by_cases hx : x ∈ P <;> simp_all [rootedSpan]
 | node l r => simp only [rootedSpan] at *; split at * <;> simp_all

theorem rooted_overlap (A B : List Nat) (t : Tree) :
 Overlap (rootedSpan A t) (rootedSpan B t) ↔ rootedSpan A t ≠ [] ∧ rootedSpan B t ≠ [] := by
 constructor
 · rintro ⟨v,hv,hw⟩; constructor <;> intro he <;> simp_all
 · rintro ⟨ha,hb⟩; exact ⟨[],rooted_root_of_nonempty A t ha,rooted_root_of_nonempty B t hb⟩

theorem state_has (A B : List Nat) (t : Tree) :
 ((hullState A B t).a = true ↔ rootedSpan A t ≠ []) ∧
 ((hullState A B t).b = true ↔ rootedSpan B t ≠ []) := by
 induction t with
 | leaf x => simp [hullState,rootedSpan] <;> grind
 | node l r ihl ihr =>
   cases ha : rootedSpan A l <;> cases hb : rootedSpan A r <;>
    cases hc : rootedSpan B l <;> cases hd : rootedSpan B r <;>
    simp_all [hullState,join,rootedSpan]

theorem state_semantics (A B : List Nat) (t : Tree) :
 ((hullState A B t).ab = true ↔ Overlap (rootedSpan A t) (minimalVertices B t)) ∧
 ((hullState A B t).ba = true ↔ Overlap (rootedSpan B t) (minimalVertices A t)) ∧
 ((hullState A B t).mm = true ↔ Overlap (minimalVertices A t) (minimalVertices B t)) := by
 induction t with
 | leaf x => by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [hullState,rootedSpan,minimalVertices,ha,hb,Overlap]
 | node l r ihl ihr =>
   have hhl := state_has A B l
   have hhr := state_has A B r
   have mal := minimal_empty_of_rooted_empty A l
   have mar := minimal_empty_of_rooted_empty A r
   have mbl := minimal_empty_of_rooted_empty B l
   have mbr := minimal_empty_of_rooted_empty B r
   cases hal : rootedSpan A l <;> cases har : rootedSpan A r <;>
    cases hbl : rootedSpan B l <;> cases hbr : rootedSpan B r <;>
    simp_all [hullState,join,rootedSpan,minimalVertices,overlap_comm] <;> grind

#print axioms state_semantics
end OriginalEdgeClipping

namespace OriginalEdgeClipping
open RMAF

def optionState (A B : List Nat) : Option Tree → HullState
 | none => zero
 | some t => hullState A B t

theorem state_restrict (t : Tree) (P A B : List Nat)
 (ha : ∀ x, x ∈ A → x ∈ P) (hb : ∀ x, x ∈ B → x ∈ P) :
 optionState A B (restrict P t) = hullState A B t := by
 induction t with
 | leaf x =>
   by_cases hp : x ∈ P
   · simp [restrict,optionState,hullState,hp]
   · have hna : x ∉ A := fun hx => hp (ha x hx)
     have hnb : x ∉ B := fun hx => hp (hb x hx)
     simp [restrict,optionState,hullState,zero,hp,hna,hnb]
 | node l r ihl ihr =>
   cases hl : restrict P l <;> cases hr : restrict P r <;>
    (simp only [hl,hr,optionState] at ihl ihr
     simp only [restrict,hl,hr,optionState,hullState]
     rw [← ihl,← ihr] <;>
     simp [join_zero_left,join_zero_right])

theorem sameShape_state (t u : Tree) (A B : List Nat) (h : sameShape t u = true) :
 hullState A B t = hullState A B u := by
 induction t generalizing u with
 | leaf x =>
   cases u with
   | leaf y => have he : x = y := beq_iff_eq.mp h; subst y; rfl
   | node v w => simp [sameShape] at h
 | node l r ihl ihr =>
   cases u with
   | leaf y => simp [sameShape] at h
   | node v w =>
     simp only [sameShape,Bool.or_eq_true,Bool.and_eq_true] at h
     rcases h with h|h
     · simp only [hullState,ihl v h.1,ihr w h.2]
     · simpa only [hullState,ihl w h.1,ihr v h.2] using join_comm (hullState A B w) (hullState A B v)

theorem disjoint_iff_not_overlap (V W : List RMAF.Vertex) :
 disjointVertices V W = true ↔ ¬ Overlap V W := by
 simp [disjointVertices,Overlap,List.all_eq_true,List.contains_iff_mem] <;> grind

theorem subblock_separation_transport (T S : Tree) (P A B : List Nat)
 (h : restrictionAgrees T S P = true)
 (ha : ∀ x, x ∈ A → x ∈ P) (hb : ∀ x, x ∈ B → x ∈ P) :
 disjointVertices (minimalVertices A T) (minimalVertices B T) = true ↔
 disjointVertices (minimalVertices A S) (minimalVertices B S) = true := by
 cases ht : restrict P T with
 | none => simp [restrictionAgrees,ht] at h
 | some t =>
   cases hs : restrict P S with
   | none => simp [restrictionAgrees,ht,hs] at h
   | some s =>
     have hshape : sameShape t s = true := by simpa [restrictionAgrees,ht,hs] using h
     have hstate := sameShape_state t s A B hshape
     have hT := state_restrict T P A B ha hb
     have hS := state_restrict S P A B ha hb
     simp only [ht,hs,optionState] at hT hS
     have he : hullState A B T = hullState A B S := hT.symm.trans (hstate.trans hS)
     rw [disjoint_iff_not_overlap,disjoint_iff_not_overlap]
     rw [← (state_semantics A B T).2.2, ← (state_semantics A B S).2.2,he]

#print axioms state_restrict
#print axioms sameShape_state
#print axioms subblock_separation_transport
end OriginalEdgeClipping

namespace OriginalEdgeClipping
open RMAF Universal233.CoreGraph GenericG0Exchange

theorem state_ba_false_of_rootedA_empty (A B : List Nat) (t : Tree)
 (h : rootedSpan A t = []) : (hullState A B t).a = false ∧ (hullState A B t).ba = false := by
 have hm := minimal_empty_of_rooted_empty A t h
 have ha := (state_has A B t).1
 have hb := (state_semantics A B t).2.1
 cases ea : (hullState A B t).a <;> cases eb : (hullState A B t).ba <;> simp_all

theorem subtree_inner_outer_state (t u : Tree) (q : RMAF.Vertex) (A B : List Nat)
 (hn : (leaves t).Nodup) (hs : subtree t q = some u)
 (ha : ∀ x, x ∈ A → x ∈ leaves u)
 (hb : ∀ x, x ∈ leaves u → x ∉ B) : (hullState A B t).ba = false := by
 induction q generalizing t with
 | nil =>
   have he : t = u := by simpa [subtree] using hs
   subst u
   have hr := G0Resume.rooted_empty_of_disjoint B t hb
   have hm := (state_semantics A B t).2.1
   cases ee : (hullState A B t).ba <;> simp_all
 | cons s q ih =>
   cases t with
   | leaf x => simp [subtree] at hs
   | node l r =>
     simp only [leaves,List.nodup_append] at hn
     cases s with
     | false =>
       have hi := ih l hn.1 hs
       have hna : ∀ x ∈ leaves r, x ∉ A := by
         intro x hxr hxa
         have hxl := (subtree_leaves_sublist l q u hs).subset (ha x hxa)
         exact hn.2.2 x hxl x hxr rfl
       have hr := G0Resume.rooted_empty_of_disjoint A r hna
       have hz := state_ba_false_of_rootedA_empty A B r hr
       simp [hullState,join,hi,hz.1,hz.2]
     | true =>
       have hi := ih r hn.2.1 hs
       have hna : ∀ x ∈ leaves l, x ∉ A := by
         intro x hxl hxa
         have hxr := (subtree_leaves_sublist r q u hs).subset (ha x hxa)
         exact hn.2.2 x hxl x hxr rfl
       have hl := G0Resume.rooted_empty_of_disjoint A l hna
       have hz := state_ba_false_of_rootedA_empty A B l hl
       simp [hullState,join,hi,hz.1,hz.2]

theorem subtree_inner_outer_separation (t u : Tree) (q : RMAF.Vertex) (A B : List Nat)
 (hn : (leaves t).Nodup) (hs : subtree t q = some u)
 (ha : ∀ x, x ∈ A → x ∈ leaves u)
 (hb : ∀ x, x ∈ leaves u → x ∉ B) :
 disjointVertices (minimalVertices A t) (minimalVertices B t) = true := by
 have hz := subtree_inner_outer_state t u q A B hn hs ha hb
 rw [disjoint_iff_not_overlap]
 rintro ⟨v,hva,hvb⟩
 have hroot := G0Resume.minimal_subset_rooted B t v hvb
 have hstate := (state_semantics A B t).2.1.mpr ⟨v,hroot,hva⟩
 simp [hz] at hstate

theorem same_old_block_pieces_separated (T S U : Tree) (q : RMAF.Vertex) (P : List Nat)
 (hn : (leaves S).Nodup) (hs : subtree S q = some U)
 (hp : restrictionAgrees T S P = true) :
 let A := BinaryExchange.yes P (leaves U).contains
 let B := BinaryExchange.no P (leaves U).contains
 disjointVertices (minimalVertices A T) (minimalVertices B T) = true ∧
 disjointVertices (minimalVertices A S) (minimalVertices B S) = true := by
 intro A B
 have ha : ∀ x, x ∈ A → x ∈ P := by intro x hx; exact (List.mem_filter.mp hx).1
 have hb : ∀ x, x ∈ B → x ∈ P := by intro x hx; exact (List.mem_filter.mp hx).1
 have has : ∀ x, x ∈ A → x ∈ leaves U := by
   intro x hx; simpa [A,BinaryExchange.yes,List.contains_iff_mem] using (List.mem_filter.mp hx).2
 have hbs : ∀ x, x ∈ leaves U → x ∉ B := by
   intro x hx hxb
   have := (List.mem_filter.mp hxb).2
   simp [B,BinaryExchange.no,List.contains_iff_mem,hx] at this
 have hd := subtree_inner_outer_separation S U q A B hn hs has hbs
 exact ⟨(subblock_separation_transport T S P A B hp ha hb).mpr hd,hd⟩

#print axioms subtree_inner_outer_state
#print axioms subtree_inner_outer_separation
#print axioms same_old_block_pieces_separated
end OriginalEdgeClipping

namespace OriginalEdgeClipping
open RMAF BinaryExchange

theorem split_mem (P Q : List Nat) (f : Nat → Bool) :
 Q ∈ split P f ↔ Q ≠ [] ∧ (Q = yes P f ∨ Q = no P f) := by
 simp [split,List.mem_filter,List.isEmpty_iff] <;> grind

theorem split_subset (P Q : List Nat) (f : Nat → Bool) (h : Q ∈ split P f) :
 ∀ x, x ∈ Q → x ∈ P := by
 rcases (split_mem P Q f).mp h with ⟨_,he|he⟩ <;> subst Q <;>
  intro x hx <;> exact (List.mem_filter.mp hx).1

theorem split_flatten (P : List Nat) (f : Nat → Bool) :
 (split P f).flatten = yes P f ++ no P f := by
 cases hy : yes P f <;> cases hn : no P f <;> simp [split,hy,hn]

theorem splitAll_flatten_perm (G : List (List Nat)) (f : Nat → Bool) :
 (splitAll G f).flatten.Perm G.flatten := by
 induction G with
 | nil => simp [splitAll]
 | cons P G ih =>
   simpa [splitAll,List.flatMap_cons,List.flatten_append,split_flatten,yes,no]
    using (List.filter_append_perm f P).append ih

theorem splitAll_partition (L : List Nat) (G : List (List Nat)) (f : Nat → Bool)
 (h : partitionCheck L G = true) : partitionCheck L (splitAll G f) = true := by
 have hp := splitAll_flatten_perm G f
 simp only [partitionCheck,Bool.and_eq_true] at h ⊢
 refine ⟨⟨?_,?_⟩,?_⟩
 · apply List.all_eq_true.mpr
   intro Q hQ
   obtain ⟨P,_,hPQ⟩ := List.mem_flatMap.mp hQ
   have hn := ((split_mem P Q f).mp hPQ).1
   simpa [List.isEmpty_iff] using hn
 · apply List.all_eq_true.mpr
   intro x hx
   have he := List.all_eq_true.mp h.1.2 x hx
   simpa [hp.count_eq x] using he
 · apply List.all_eq_true.mpr
   intro x hx
   exact List.all_eq_true.mp h.2 x (hp.mem_iff.mp hx)

theorem pairwiseEmbeddings_iff (t : Tree) (F : List (List Nat)) :
 pairwiseEmbeddings t F = true ↔
 F.Pairwise (fun P Q => disjointVertices (minimalVertices P t) (minimalVertices Q t) = true) := by
 induction F with
 | nil => simp [pairwiseEmbeddings]
 | cons P F ih => simp [pairwiseEmbeddings,List.pairwise_cons,List.all_eq_true,ih]

theorem splitAll_embeddings (t : Tree) (G : List (List Nat)) (f : Nat → Bool)
 (h : pairwiseEmbeddings t G = true)
 (hi : ∀ P ∈ G, disjointVertices (minimalVertices (yes P f) t) (minimalVertices (no P f) t) = true) :
 pairwiseEmbeddings t (splitAll G f) = true := by
 apply (pairwiseEmbeddings_iff t _).mpr
 apply List.pairwise_flatMap.mpr
 constructor
 · intro P hP
   have hd := hi P hP
   apply List.Pairwise.filter
   simp [List.pairwise_cons,hd]
 · apply ((pairwiseEmbeddings_iff t G).mp h).imp
   intro P Q hd A hA B hB
   rw [disjoint_iff_not_overlap]
   rintro ⟨v,hva,hvb⟩
   exact RootSpanMonotonicity.subblocks_no_common t P Q A B
    (split_subset P A f hA) (split_subset Q B f hB) hd v hva hvb

theorem agreement_original_source_edge (T S U : Tree) (G : List (List Nat)) (q : RMAF.Vertex)
 (hT : (leaves T).Nodup) (hS : (leaves S).Nodup)
 (h : agreement T S G = true) (hs : Universal233.CoreGraph.subtree S q = some U) :
 agreement T S (splitAll G (leaves U).contains) = true := by
 have hh := h
 simp only [agreement,Bool.and_eq_true] at hh ⊢
 rcases hh with ⟨⟨⟨⟨hpT,hpS⟩,hshape⟩,hembT⟩,hembS⟩
 have hint : ∀ P ∈ G,
  disjointVertices (minimalVertices (yes P (leaves U).contains) T) (minimalVertices (no P (leaves U).contains) T) = true ∧
  disjointVertices (minimalVertices (yes P (leaves U).contains) S) (minimalVertices (no P (leaves U).contains) S) = true := by
   intro P hP
   exact same_old_block_pieces_separated T S U q P hS hs (List.all_eq_true.mp hshape P hP)
 refine ⟨⟨⟨⟨splitAll_partition _ _ _ hpT,splitAll_partition _ _ _ hpS⟩,?_⟩,
  splitAll_embeddings _ _ _ hembT (fun P hP => (hint P hP).1)⟩,
  splitAll_embeddings _ _ _ hembS (fun P hP => (hint P hP).2)⟩
 apply List.all_eq_true.mpr
 intro Q hQ
 obtain ⟨P,hP,hPQ⟩ := List.mem_flatMap.mp hQ
 have hsub := split_subset P Q (leaves U).contains hPQ
 have hne := ((split_mem P Q (leaves U).contains).mp hPQ).1
 have hx : ∃ x ∈ Q, x ∈ leaves T := by
   obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil Q hne
   have hpflat : x ∈ G.flatten := List.mem_flatten.mpr ⟨P,hP,hsub x hx⟩
   have hpa := hpT
   simp only [partitionCheck,Bool.and_eq_true] at hpa
   have ht := List.all_eq_true.mp hpa.2 x hpflat
   exact ⟨x,hx,by simpa [List.contains_iff_mem] using ht⟩
 exact RootRestrictionHeredity.restrictionAgrees_subset T S P Q
  (List.all_eq_true.mp hshape P hP) hsub hx

#print axioms splitAll_partition
#print axioms splitAll_embeddings
#print axioms agreement_original_source_edge
end OriginalEdgeClipping

namespace OriginalEdgeClipping
open RMAF BinaryExchange

theorem sameShape_comm (t u : Tree) : sameShape t u = sameShape u t := by
 induction t generalizing u with
 | leaf x => cases u <;> simp [sameShape,BEq.comm]
 | node l r ihl ihr =>
   cases u with
   | leaf x => simp [sameShape]
   | node v w => simp only [sameShape,← ihl v,← ihl w,← ihr v,← ihr w,Bool.and_comm]

theorem restrictionAgrees_comm (t u : Tree) (P : List Nat) :
 restrictionAgrees t u P = restrictionAgrees u t P := by
 cases ht : restrict P t <;> cases hu : restrict P u <;>
  simp [restrictionAgrees,ht,hu,sameShape_comm]

theorem agreement_comm (t u : Tree) (G : List (List Nat)) : agreement t u G = agreement u t G := by
 have hf : restrictionAgrees t u = restrictionAgrees u t := by
   funext P; exact restrictionAgrees_comm t u P
 simp only [agreement,hf]
 ac_rfl

theorem agreement_original_target_edge (T S U : Tree) (G : List (List Nat)) (q : RMAF.Vertex)
 (hT : (leaves T).Nodup) (hS : (leaves S).Nodup)
 (h : agreement T S G = true) (ht : Universal233.CoreGraph.subtree T q = some U) :
 agreement T S (splitAll G (leaves U).contains) = true := by
 rw [agreement_comm]
 exact agreement_original_source_edge S T U G q hS hT (by simpa only [agreement_comm T S] using h) ht

namespace InterfaceControls

def t : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def u : Tree := .node (.leaf 0) (.leaf 1)
def G : List (List Nat) := [[0,1,2,3]]
example : agreement t t (splitAll G [0,1].contains) = true := by
 exact agreement_original_source_edge t t u G [false] (by decide) (by decide) (by decide) rfl
example : agreement t t (splitAll G [0,1].contains) = true := by
 exact agreement_original_target_edge t t u G [false] (by decide) (by decide) (by decide) rfl
example : agreement t t (splitAll G (leaves t).contains) = true := by
 exact agreement_original_source_edge t t t G [] (by decide) (by decide) (by decide) rfl
end InterfaceControls

#print axioms agreement_original_source_edge
#print axioms agreement_original_target_edge
end OriginalEdgeClipping

namespace G0PureHardControls
open RMAF BinaryExchange G0Singleton G0SingletonCoreFixture
open Universal233.CherryBranching
def Fs : List (List Nat) := [[0],[1],[2],[3,4],[5]]
def F2 : List (List Nat) := splitAll (splitAll G2 [2].contains) (leaves X).contains
example : agreement T S Fs = true := by decide
example : agreement T S (absorbA Fs 0 1) = true := by decide
example : (absorbA Fs 0 1).length+1 = Fs.length := by decide
example : pendantPartition S 0 1 = [[3,4],[2],[0,1,5]] := by decide
example : F2 = [[0],[2],[4],[1],[3],[5]] := by decide
example : agreement T S F2 = true := by decide
example : agreement T S (absorbA F2 0 1) = true := by decide
example : [0] ∈ F2 := by decide
example : [1] ∈ F2 := by decide
example : (absorbA F2 0 1).length = G2.length+1 := by decide
#eval "PURE_HARD_CONTROLS 10/10 PASS; singleton-b and exceptional cut debt retained"
end G0PureHardControls

namespace G0PureHardMerge
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.CherryBranching Universal233.Rule5Case322 VertexGeometry
open G0Resume G0Shared G0Singleton G0CoreAbsorption GenericG0Exchange

-- No assumption on the b-block is present. In particular [b] may be in F.
theorem pure_hard_merge {T S : Tree} (D : LiteralGeometry T S)
    (F : List (List Nat)) (hf : agreement T S F = true) (ha : [D.a] ∈ F)
    (href : Refines F (pendantPartition S D.a D.b)) :
    let K := absorbA F D.a D.b
    agreement T S K = true ∧ K.length+1 = F.length ∧
      K.length = F.length-1 ∧ K.length < F.length ∧
      Refines K (hardBranch S D.a D.b).partition ∧
      hardBranch S D.a D.b ∈ guardedPlan D := by
  have h := hf
  simp only [agreement,Bool.and_eq_true] at h
  have hbT := (actual_cherry_labels T D.a D.b D.cherry).2
  obtain ⟨B,hB,hbB⟩ := partition_block_exists (leaves T) F h.1.1.1.1 D.b hbT
  have hc := pure_b_block_core D B hbB (href B hB)
  have hAF := pure_core_absorb_agreement D F hf ha href
  have hlen := absorbA_length F D.a D.b ha
  have hRef := absorbA_refines_pendant D F hf href B hB hbB hc
  exact ⟨hAF,hlen,by omega,by omega,hRef,literal_hard_branch_mem D⟩

#print axioms pure_hard_merge
end G0PureHardMerge

namespace G0PureHardMerge
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.Case322PaidGuard
open Universal233.Case322Extraction Universal233.CherryBranching Universal233.Rule5Case322
open G0Resume G0Shared G0Singleton G0CoreAbsorption GenericG0Exchange VertexGeometry BinaryExchange

-- The two split operations keep exactly the requested literal order.
def hardPrepared {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) : List (List Nat) :=
  splitAll (splitAll G [D.c].contains) (leaves D.X).contains

theorem singleton_split_identity (a : Nat) (f : Nat → Bool) : split [a] f = [[a]] := by
  cases he : f a <;> simp [split,yes,no,he]

theorem singleton_survives_split (G : List (List Nat)) (a : Nat) (f : Nat → Bool)
    (ha : [a] ∈ G) : [a] ∈ splitAll G f := by
  apply List.mem_flatMap.mpr
  exact ⟨[a],ha,by simp [singleton_split_identity]⟩

theorem hard_prepared_agreement {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) :
    agreement T S (hardPrepared D G) = true := by
  have hc := OriginalEdgeClipping.agreement_original_source_edge T S (.leaf D.c) G
    (cArc D.w D.sc D.sb) D.properT D.properS hg (source_c_address D)
  have hc' : agreement T S (splitAll G [D.c].contains) = true := by
    simpa only [leaves] using hc
  exact OriginalEdgeClipping.agreement_original_source_edge T S D.X
    (splitAll G [D.c].contains) (xArc D.w D.sa D.sc D.sb)
    D.properT D.properS hc' (source_x_address D)

theorem hard_prepared_singleton_a {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (ha : [D.a] ∈ G) : [D.a] ∈ hardPrepared D G := by
  exact singleton_survives_split _ D.a _ (singleton_survives_split G D.a _ ha)

theorem hard_cells_members {T S : Tree} (D : LiteralGeometry T S) :
    leaves D.X ∈ pendantPartition S D.a D.b ∧
    [D.c] ∈ pendantPartition S D.a D.b ∧
    coreLabels S D.a D.b ∈ pendantPartition S D.a D.b := by
  rcases literal_pendant_partition_orders D with hp | hp <;> simp [hp]

theorem hard_prepared_refines {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) :
    Refines (hardPrepared D G) (pendantPartition S D.a D.b) := by
  have h := hg
  simp only [agreement,Bool.and_eq_true] at h
  have hcov := partition_flat_coverage (leaves S) G h.1.1.1.2
  have hcells := hard_cells_members D
  intro P hP
  obtain ⟨Q,hQ,hPQ⟩ := List.mem_flatMap.mp hP
  have hPsub := OriginalEdgeClipping.split_subset Q P (leaves D.X).contains hPQ
  rcases (OriginalEdgeClipping.split_mem Q P (leaves D.X).contains).mp hPQ with ⟨_,he|he⟩
  · refine ⟨leaves D.X,hcells.1,?_⟩
    intro x hx
    rw [he] at hx
    simpa [yes] using (List.mem_filter.mp hx).2
  · have hPX : ∀ x ∈ P, x ∉ leaves D.X := by
      intro x hx
      rw [he] at hx
      simpa [no] using (List.mem_filter.mp hx).2
    obtain ⟨R,hR,hQR⟩ := List.mem_flatMap.mp hQ
    have hQsub := OriginalEdgeClipping.split_subset R Q [D.c].contains hQR
    rcases (OriginalEdgeClipping.split_mem R Q [D.c].contains).mp hQR with ⟨_,heQ|heQ⟩
    · refine ⟨[D.c],hcells.2.1,?_⟩
      intro x hx
      have hxQ := hPsub x hx
      rw [heQ] at hxQ
      simpa [yes] using (List.mem_filter.mp hxQ).2
    · refine ⟨coreLabels S D.a D.b,hcells.2.2,?_⟩
      intro x hx
      have hxQ := hPsub x hx
      have hxR := hQsub x hxQ
      have hxS := hcov x (List.mem_flatten.mpr ⟨R,hR,hxR⟩)
      have hxc : x ≠ D.c := by
        rw [heQ] at hxQ
        simpa [no] using (List.mem_filter.mp hxQ).2
      exact (literal_core_mem_iff D x).mpr ⟨hxS,hPX x hx,hxc⟩

theorem hard_prepared_merge {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (ha : [D.a] ∈ G) :
    let F := splitAll (splitAll G [D.c].contains) (leaves D.X).contains
    let K := absorbA F D.a D.b
    agreement T S F = true ∧ [D.a] ∈ F ∧
      Refines F (hardBranch S D.a D.b).partition ∧
      agreement T S K = true ∧ K.length+1 = F.length ∧
      K.length = F.length-1 ∧ K.length < F.length ∧
      Refines K (hardBranch S D.a D.b).partition ∧
      hardBranch S D.a D.b ∈ guardedPlan D := by
  have hF := hard_prepared_agreement D G hg
  have haF := hard_prepared_singleton_a D G ha
  have hRef := hard_prepared_refines D G hg
  have hm := pure_hard_merge D (hardPrepared D G) hF haF hRef
  exact ⟨hF,haF,hRef,hm⟩

#print axioms singleton_survives_split
#print axioms hard_prepared_agreement
#print axioms hard_prepared_refines
#print axioms hard_prepared_merge
end G0PureHardMerge

namespace G0PureHardMergeConsumers
open RMAF G0Singleton G0SingletonCoreFixture G0PureHardMerge G0PureHardControls
open Universal233.CherryBranching Universal233.Rule5Case322 VertexGeometry

theorem singleton_b_fixture_refines : Refines Fs (pendantPartition S 0 1) := by
  have hp : pendantPartition S 0 1 = [[3,4],[2],[0,1,5]] := by decide
  rw [hp]
  simp [Refines,Fs]

-- This actual consumer calls the universal theorem with [b] already in F.
example : agreement T S (absorbA Fs 0 1) = true := by
  exact (pure_hard_merge D Fs (by decide) (by decide) singleton_b_fixture_refines).1
example : (absorbA Fs 0 1).length+1 = Fs.length := by
  exact (pure_hard_merge D Fs (by decide) (by decide) singleton_b_fixture_refines).2.1

-- G2 has b,c and an X-label in one original block. The consumer supplies no
-- core-B or nonsingleton-b-after-clipping assumption to the generic proof.
example : agreement T S (absorbA F2 0 1) = true := by
  have hm := hard_prepared_merge D G2 (by decide) (by decide)
  exact hm.2.2.2.1
example : (absorbA F2 0 1).length+1 = F2.length := by
  have hm := hard_prepared_merge D G2 (by decide) (by decide)
  exact hm.2.2.2.2.1
example : Refines (absorbA F2 0 1) (hardBranch S 0 1).partition := by
  have hm := hard_prepared_merge D G2 (by decide) (by decide)
  rcases hm with ⟨_,_,_,_,_,_,_,href,_⟩
  exact href
#eval "PURE_HARD_CONSUMERS_PASS full31 singleton-b pure merge and originally c+X b-block preparation composed"
end G0PureHardMergeConsumers

namespace RootHardCutDebt
open RMAF Universal233.CoreGraph Universal233.HardParent
open Universal233.Case322Extraction Universal233.Case322PaidGuard
open GenericG0Exchange G0Resume G0Shared BinaryExchange

theorem source_b_parent {T S : Tree} (D : LiteralGeometry T S) (P : List Nat)
    (hb : D.b ∈ P) (x : Nat) (hx : x ∈ P) (hxS : x ∈ leaves S) (hne : x ≠ D.b) :
    D.w ∈ minimalVertices P S := by
  have hs : subtree S D.w = some
      (orient (!D.sb) (.leaf D.b) (VC D.sa D.sc D.a D.c D.X)) := by
    rw [D.source]
    cases D.sb <;> rfl
  exact pendant_parent_crossing P S (.leaf D.b) _ D.w (!D.sb) hs D.b x
    (by simp [leaves]) hb hxS hx (by simpa [leaves] using hne)

theorem source_c_parent {T S : Tree} (D : LiteralGeometry T S) (P : List Nat)
    (hc : D.c ∈ P) (x : Nat) (hx : x ∈ P) (hxS : x ∈ leaves S) (hne : x ≠ D.c) :
    D.w ++ [D.sb] ∈ minimalVertices P S := by
  have hs : subtree S (D.w ++ [D.sb]) = some
      (orient (!D.sc) (.leaf D.c) (AX D.sa D.a D.X)) := by
    rw [source_vc_address D]
    cases D.sc <;> rfl
  exact pendant_parent_crossing P S (.leaf D.c) _ _ (!D.sc) hs D.c x
    (by simp [leaves]) hc hxS hx (by simpa [leaves] using hne)

theorem source_b_x_vc {T S : Tree} (D : LiteralGeometry T S) (P : List Nat)
    (hb : D.b ∈ P) (x : Nat) (hx : x ∈ P) (hxX : x ∈ leaves D.X) :
    D.w ++ [D.sb] ∈ minimalVertices P S := by
  rcases source_label_separation D with ⟨hab,hac,hbc,haX,hbX,hcX⟩
  have hxin : x ∈ leaves (VC D.sa D.sc D.a D.c D.X) := by
    cases D.sa <;> cases D.sc <;> simp [VC,AX,orient,leaves,hxX]
  have hbout : D.b ∉ leaves (VC D.sa D.sc D.a D.c D.X) := by
    cases D.sa <;> cases D.sc <;>
      simp [VC,AX,orient,leaves,hbX,Ne.symm hab,hbc]
  have hbS : D.b ∈ leaves S :=
    (subtree_leaves_sublist S _ _ (source_b_address D)).subset (by simp [leaves])
  exact subtree_root_crossing P S _ _ (source_vc_address D) x D.b hxin hx hbS hb hbout

theorem block_other_member {T S : Tree} (G : List (List Nat))
    (hg : agreement T S G = true) (B : List Nat) (hB : B ∈ G) (b : Nat)
    (hb : b ∈ B) (hbs : [b] ∉ G) : ∃ x ∈ B, x ≠ b ∧ x ∈ leaves S := by
  have hp : partitionCheck (leaves S) G = true := by
    simp only [agreement,Bool.and_eq_true] at hg
    exact hg.1.1.1.2
  have hflat := partition_flat_nodup (leaves S) G hp
  rcases singleton_or_other B b (block_nodup G hflat B hB) hb with he | ⟨x,hx,hne⟩
  · subst B
    exact False.elim (hbs hB)
  · exact ⟨x,hx,hne,partition_flat_coverage _ _ hp x (List.mem_flatten.mpr ⟨B,hB,hx⟩)⟩

theorem b_block_spans_w {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat))
    (hg : agreement T S G = true) (B : List Nat) (hB : B ∈ G)
    (hb : D.b ∈ B) (hbs : [D.b] ∉ G) : D.w ∈ minimalVertices B S := by
  obtain ⟨x,hx,hne,hxS⟩ := block_other_member G hg B hB D.b hb hbs
  exact source_b_parent D B hb x hx hxS hne

theorem b_meets_X_forces_singleton_c {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (B : List Nat)
    (hB : B ∈ G) (hb : D.b ∈ B) (hcB : D.c ∉ B)
    (hx : ∃ x ∈ B, x ∈ leaves D.X) : [D.c] ∈ G := by
  apply Classical.byContradiction
  intro hcs
  have hp : partitionCheck (leaves S) G = true := by
    simp only [agreement,Bool.and_eq_true] at hg
    exact hg.1.1.1.2
  have he : pairwiseEmbeddings S G = true := by
    simp only [agreement,Bool.and_eq_true] at hg
    exact hg.2
  have hcS : D.c ∈ leaves S :=
    (subtree_leaves_sublist S _ _ (source_c_address D)).subset (by simp [leaves])
  obtain ⟨C,hC,hc⟩ := partition_block_exists (leaves S) G hp D.c hcS
  obtain ⟨y,hy,hyne,hyS⟩ := block_other_member G hg C hC D.c hc hcs
  have hBC : B ≠ C := by intro h; subst C; exact hcB hc
  obtain ⟨x,hxB,hxX⟩ := hx
  exact pairwise_no_common S G he B C hB hC hBC _
    (source_b_x_vc D B hb x hxB hxX) (source_c_parent D C hc y hy hyS hyne)

#print axioms source_b_parent
#print axioms source_c_parent
#print axioms b_block_spans_w
#print axioms b_meets_X_forces_singleton_c
end RootHardCutDebt

namespace RootHardCutDebt
open RMAF Universal233.CoreGraph Universal233.Case322Extraction Universal233.Case322PaidGuard
open GenericG0Exchange G0Resume G0Shared BinaryExchange

theorem overlapping_blocks_equal (G : List (List Nat)) (hn : G.flatten.Nodup)
    (P Q : List Nat) (hp : P ∈ G) (hq : Q ∈ G) (x : Nat)
    (hxp : x ∈ P) (hxq : x ∈ Q) : P = Q := by
  induction G with
  | nil => simp at hp
  | cons A G ih =>
    simp only [List.flatten_cons,List.nodup_append] at hn
    rcases List.mem_cons.mp hp with heP | hp
    · subst P
      rcases List.mem_cons.mp hq with heQ | hq
      · exact heQ.symm
      · exact False.elim (hn.2.2 x hxp x (List.mem_flatten.mpr ⟨Q,hq,hxq⟩) rfl)
    · rcases List.mem_cons.mp hq with heQ | hq
      · subst Q
        exact False.elim (hn.2.2 x hxq x (List.mem_flatten.mpr ⟨P,hp,hxp⟩) rfl)
      · exact ih hn.2.1 hp hq

theorem mixed_X_core_block_is_B {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (ha : [D.a] ∈ G)
    (hbs : [D.b] ∉ G) (B : List Nat) (hB : B ∈ G) (hb : D.b ∈ B)
    (P : List Nat) (hP : P ∈ G) (x y : Nat)
    (hxP : x ∈ P) (hxX : x ∈ leaves D.X) (hyP : y ∈ P)
    (hyX : y ∉ leaves D.X) (hyc : y ≠ D.c) : P = B := by
  have hp : partitionCheck (leaves S) G = true := by
    simp only [agreement,Bool.and_eq_true] at hg
    exact hg.1.1.1.2
  have hflat := partition_flat_nodup _ _ hp
  rcases source_label_separation D with ⟨hab,hac,hbc,haX,hbX,hcX⟩
  by_cases hya : y = D.a
  · subst y
    have hEq := singleton_block_isolated G D.a hflat ha P hP hyP
    have hxa : x = D.a := by simpa [hEq] using hxP
    subst x
    exact False.elim (haX hxX)
  by_cases hyb : y = D.b
  · subst y
    exact overlapping_blocks_equal G hflat P B hP hB D.b hyP hb
  by_cases hPB : P = B
  · exact hPB
  have hxin : x ∈ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) := by
    cases D.sa <;> cases D.sc <;> cases D.sb <;>
      simp [bottom,VC,AX,orient,leaves,hxX]
  have hyout : y ∉ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) := by
    cases D.sa <;> cases D.sc <;> cases D.sb <;>
      simp [bottom,VC,AX,orient,leaves,hya,hyb,hyc,hyX]
  have hyS := partition_flat_coverage _ _ hp y (List.mem_flatten.mpr ⟨P,hP,hyP⟩)
  have hwP := subtree_root_crossing P S _ D.w D.source x y hxin hxP hyS hyP hyout
  have hwB := b_block_spans_w D G hg B hB hb hbs
  have he : pairwiseEmbeddings S G = true := by
    simp only [agreement,Bool.and_eq_true] at hg
    exact hg.2
  exact False.elim (pairwise_no_common S G he P B hP hB hPB D.w hwP hwB)

theorem no_X_mix_except_c {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (ha : [D.a] ∈ G)
    (hbs : [D.b] ∉ G) (B : List Nat) (hB : B ∈ G) (hb : D.b ∈ B)
    (hnex : ¬(D.c ∈ B ∧ ∃ x ∈ B, x ∈ leaves D.X)) (hcs : [D.c] ∉ G) :
    ∀ P ∈ G, ∀ x ∈ P, x ∈ leaves D.X → ∀ y ∈ P, y ∉ leaves D.X → y = D.c := by
  have hBX : ∀ x ∈ B, x ∉ leaves D.X := by
    intro x hxB hxX
    have hcB : D.c ∉ B := fun hc => hnex ⟨hc,x,hxB,hxX⟩
    exact hcs (b_meets_X_forces_singleton_c D G hg B hB hb hcB ⟨x,hxB,hxX⟩)
  intro P hP x hxP hxX y hyP hyX
  by_cases hyc : y = D.c
  · exact hyc
  have hPB := mixed_X_core_block_is_B D G hg ha hbs B hB hb P hP x y hxP hxX hyP hyX hyc
  subst P
  exact False.elim (hBX x hxP hxX)

#print axioms overlapping_blocks_equal
#print axioms mixed_X_core_block_is_B
#print axioms no_X_mix_except_c
end RootHardCutDebt

namespace RootHardCutDebt
open RMAF Universal233.CoreGraph Universal233.Case322Extraction Universal233.Case322PaidGuard
open GenericG0Exchange G0Resume G0Shared G0CutExchangePrefix BinaryExchange

theorem split_of_uniform (P : List Nat) (f : Nat → Bool) (hne : P ≠ [])
    (h : (∀ x ∈ P, f x = true) ∨ (∀ x ∈ P, f x = false)) : split P f = [P] := by
  rcases h with h | h
  · have hy : yes P f = P := List.filter_eq_self.mpr h
    have hn : no P f = [] := List.filter_eq_nil_iff.mpr (by
      intro x hx
      simp [h x hx])
    simp [split,hy,hn,hne]
  · have hy : yes P f = [] := List.filter_eq_nil_iff.mpr (by
      intro x hx
      simp [h x hx])
    have hn : no P f = P := List.filter_eq_self.mpr (by
      intro x hx
      simp [h x hx])
    simp [split,hy,hn,hne]

theorem X_cut_after_c_identity {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (ha : [D.a] ∈ G)
    (hbs : [D.b] ∉ G) (B : List Nat) (hB : B ∈ G) (hb : D.b ∈ B)
    (hnex : ¬(D.c ∈ B ∧ ∃ x ∈ B, x ∈ leaves D.X)) (hcs : [D.c] ∉ G) :
    splitAll (splitAll G [D.c].contains) (leaves D.X).contains = splitAll G [D.c].contains := by
  have hcl := no_X_mix_except_c D G hg ha hbs B hB hb hnex hcs
  have hcX : D.c ∉ leaves D.X := (source_label_separation D).2.2.2.2.2
  apply splitAll_identity_of_blocks
  intro Q hQ
  obtain ⟨P,hP,hPQ⟩ := List.mem_flatMap.mp hQ
  have hne : Q ≠ [] := by
    have hn := (List.mem_filter.mp hPQ).2
    intro h0
    subst Q
    simp at hn
  apply split_of_uniform Q (leaves D.X).contains hne
  have hcases : Q = yes P [D.c].contains ∨ Q = no P [D.c].contains := by
    have hm := (List.mem_filter.mp hPQ).1
    simpa using hm
  rcases hcases with hyes | hno
  · subst Q
    right
    intro y hy
    have hyc : y = D.c := by
      have hh := List.contains_iff_mem.mp (List.mem_filter.mp hy).2
      simpa using hh
    subst y
    simp [hcX]
  · subst Q
    by_cases hx : ∃ x ∈ no P [D.c].contains, x ∈ leaves D.X
    · left
      obtain ⟨x,hxQ,hxX⟩ := hx
      have hxP := (List.mem_filter.mp hxQ).1
      intro y hyQ
      have hyP := (List.mem_filter.mp hyQ).1
      have hyc : y ≠ D.c := by
        have hh := (List.mem_filter.mp hyQ).2
        simpa using hh
      by_cases hyX : y ∈ leaves D.X
      · simp [hyX]
      · exact False.elim (hyc (hcl P hP x hxP hxX y hyP hyX))
    · right
      intro y hyQ
      have hyX : y ∉ leaves D.X := fun hy => hx ⟨y,hyQ,hy⟩
      simp [hyX]

theorem source_one_edge_bound {T S U : Tree} (G : List (List Nat))
    (hg : agreement T S G = true) (q : RMAF.Vertex) (hs : subtree S q = some U) :
    (splitAll G (leaves U).contains).length ≤ G.length+1 := by
  have hp : partitionCheck (leaves S) G = true := by
    simp only [agreement,Bool.and_eq_true] at hg
    exact hg.1.1.1.2
  have he : pairwiseEmbeddings S G = true := by
    simp only [agreement,Bool.and_eq_true] at hg
    exact hg.2
  exact one_edge_split_adds_at_most_one S U q hs G
    (fun P hP x hx => partition_flat_coverage _ _ hp x (List.mem_flatten.mpr ⟨P,hP,hx⟩)) he

theorem hard_c_then_X_debt {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (ha : [D.a] ∈ G)
    (hbs : [D.b] ∉ G) (B : List Nat) (hB : B ∈ G) (hb : D.b ∈ B)
    (hnex : ¬(D.c ∈ B ∧ ∃ x ∈ B, x ∈ leaves D.X)) :
    (splitAll (splitAll G [D.c].contains) (leaves D.X).contains).length ≤ G.length+1 := by
  by_cases hcs : [D.c] ∈ G
  · rw [singleton_component_cut_identity G D.c hg hcs]
    exact source_one_edge_bound G hg _ (source_x_address D)
  · rw [X_cut_after_c_identity D G hg ha hbs B hB hb hnex hcs]
    simpa only [leaves] using source_one_edge_bound G hg _ (source_c_address D)

#print axioms X_cut_after_c_identity
#print axioms hard_c_then_X_debt
end RootHardCutDebt

namespace RootNonexceptionalG0
open RMAF Universal233.CoreGraph Universal233.Case322PaidGuard
open Universal233.Rule5Case322 VertexGeometry BinaryExchange G0Singleton
open GenericG0Exchange G0Resume G0Shared G0PureHardMerge RootHardCutDebt

theorem g0_of_nonexceptional_singleton_a {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) (ha : [D.a] ∈ G)
    (hbs : [D.b] ∉ G) (B : List Nat) (hB : B ∈ G) (hb : D.b ∈ B)
    (hnex : ¬(D.c ∈ B ∧ ∃ x ∈ B, x ∈ leaves D.X)) :
    ∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧
      H.length ≤ G.length ∧ Refines H child.partition := by
  have hm := hard_prepared_merge D G hg ha
  dsimp only at hm
  rcases hm with ⟨hF,haF,hrefF,hK,hlen,hminus,hless,hrefK,hmem⟩
  have hdebt := hard_c_then_X_debt D G hg ha hbs B hB hb hnex
  refine ⟨hardBranch S D.a D.b,hmem,
    absorbA (splitAll (splitAll G [D.c].contains) (leaves D.X).contains) D.a D.b,
    hK,?_,hrefK⟩
  omega

theorem g0_witness_or_exceptional {T S : Tree} (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) :
    (∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧
      H.length ≤ G.length ∧ Refines H child.partition) ∨
    ([D.a] ∈ G ∧ ∃ B ∈ G, D.b ∈ B ∧ D.c ∈ B ∧ ∃ x ∈ B, x ∈ leaves D.X) := by
  rcases g0_witness_or_a_singleton D G hg with h | ⟨hbs,hnotshared,ha⟩
  · exact Or.inl h
  have hp : partitionCheck (leaves T) G = true := by
    simp only [agreement,Bool.and_eq_true] at hg
    exact hg.1.1.1.1
  have hbT : D.b ∈ leaves T :=
    (subtree_leaves_sublist T D.ub (.leaf D.b) D.leafB).subset (by simp [leaves])
  obtain ⟨B,hB,hb⟩ := partition_block_exists (leaves T) G hp D.b hbT
  by_cases hexc : D.c ∈ B ∧ ∃ x ∈ B, x ∈ leaves D.X
  · exact Or.inr ⟨ha,B,hB,hb,hexc.1,hexc.2⟩
  · exact Or.inl (g0_of_nonexceptional_singleton_a D G hg ha hbs B hB hb hexc)

#print axioms g0_of_nonexceptional_singleton_a
#print axioms g0_witness_or_exceptional
end RootNonexceptionalG0

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping

@[simp] theorem mem_leaves_orient (s : Bool) (A B : Tree) (x : Nat) :
 x ∈ leaves (orient s A B) ↔ x ∈ leaves A ∨ x ∈ leaves B := by
 cases s <;> simp [orient,leaves,or_comm]

theorem agreeing_subblock_state (T S : Tree) (P A B : List Nat)
 (h : restrictionAgrees T S P = true)
 (ha : ∀ x, x ∈ A → x ∈ P) (hb : ∀ x, x ∈ B → x ∈ P) :
 hullState A B T = hullState A B S := by
 cases ht : restrict P T with
 | none => simp [restrictionAgrees,ht] at h
 | some t =>
   cases hs : restrict P S with
   | none => simp [restrictionAgrees,ht,hs] at h
   | some s =>
     have hshape : sameShape t s = true := by simpa [restrictionAgrees,ht,hs] using h
     have hstate := sameShape_state t s A B hshape
     have hT := state_restrict T P A B ha hb
     have hS := state_restrict S P A B ha hb
     simp only [ht,hs,optionState] at hT hS
     exact hT.symm.trans (hstate.trans hS)

theorem stem_separation_transport (T S : Tree) (P A B : List Nat)
 (h : restrictionAgrees T S P = true)
 (ha : ∀ x, x ∈ A → x ∈ P) (hb : ∀ x, x ∈ B → x ∈ P) :
 disjointVertices (rootedSpan A T) (minimalVertices B T) = true ↔
 disjointVertices (rootedSpan A S) (minimalVertices B S) = true := by
 have he := agreeing_subblock_state T S P A B h ha hb
 rw [disjoint_iff_not_overlap,disjoint_iff_not_overlap]
 rw [← (state_semantics A B T).1,← (state_semantics A B S).1,he]

theorem original_subtree_stem_separated (t u : Tree) (q : RMAF.Vertex) (A B : List Nat)
 (hn : (leaves t).Nodup) (hs : subtree t q = some u)
 (ha : ∀ x, x ∈ A → x ∈ leaves u) (hb : ∀ x, x ∈ leaves u → x ∉ B) :
 disjointVertices (rootedSpan B t) (minimalVertices A t) = true := by
 have hz := subtree_inner_outer_state t u q A B hn hs ha hb
 rw [disjoint_iff_not_overlap]
 intro h
 have hh := (state_semantics A B t).2.1.mpr h
 simp [hz] at hh

theorem agreement_block_shape (T S : Tree) (G : List (List Nat)) (P : List Nat)
 (h : agreement T S G = true) (hp : P ∈ G) : restrictionAgrees T S P = true := by
 have hh := h
 simp only [agreement,Bool.and_eq_true] at hh
 exact List.all_eq_true.mp hh.1.1.2 P hp

def xPiece {T S : Tree} (D : LiteralGeometry T S) (B : List Nat) : List Nat :=
 B.filter (leaves D.X).contains

theorem c_stem_avoids_xPiece {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (hB : B ∈ G) (hc : D.c ∈ B) :
 disjointVertices (rootedSpan [D.c] T) (minimalVertices (xPiece D B) T) = true := by
 have hp := agreement_block_shape T S G B h hB
 have hsub : ∀ x, x ∈ xPiece D B → x ∈ B := by intro x hx; exact (List.mem_filter.mp hx).1
 have hsubc : ∀ x, x ∈ [D.c] → x ∈ B := by
   intro x hx
   have he : x = D.c := by simpa using hx
   simpa [he] using hc
 have ha : ∀ x, x ∈ xPiece D B → x ∈ leaves D.X := by
   intro x hx; exact List.contains_iff_mem.mp (List.mem_filter.mp hx).2
 have hcx := (source_label_separation D).2.2.2.2.2
 have hd := original_subtree_stem_separated S D.X (xArc D.w D.sa D.sc D.sb)
  (xPiece D B) [D.c] D.properS (source_x_address D) ha (by
    intro x hx hxc
    have he : x = D.c := by simpa using hxc
    subst x
    exact hcx hx)
 exact (stem_separation_transport T S B [D.c] (xPiece D B) hp hsubc hsub).mpr hd

theorem b_stem_avoids_c_xPiece {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B) :
 disjointVertices (rootedSpan [D.b] T) (minimalVertices (D.c :: xPiece D B) T) = true := by
 have hp := agreement_block_shape T S G B h hB
 have hsub : ∀ x, x ∈ D.c :: xPiece D B → x ∈ B := by
   intro x hx; rcases List.mem_cons.mp hx with hx|hx
   · simpa [hx] using hc
   · exact (List.mem_filter.mp hx).1
 have hsubb : ∀ x, x ∈ [D.b] → x ∈ B := by
   intro x hx
   have he : x = D.b := by simpa using hx
   simpa [he] using hb
 rcases source_label_separation D with ⟨hab,hac,hbc,haX,hbX,hcX⟩
 have ha : ∀ x, x ∈ D.c :: xPiece D B → x ∈ leaves (VC D.sa D.sc D.a D.c D.X) := by
   intro x hx
   rcases List.mem_cons.mp hx with he|hx
   · subst x; simp [VC,AX,leaves]
   · have hxX := List.contains_iff_mem.mp (List.mem_filter.mp hx).2
     simp_all [VC,AX,leaves,Ne.symm hab]
 have hboff : ∀ x, x ∈ leaves (VC D.sa D.sc D.a D.c D.X) → x ∉ [D.b] := by
   intro x hx hxb
   have he : x = D.b := by simpa using hxb
   subst x
   simp_all [VC,AX,leaves,Ne.symm hab]
 have hd := original_subtree_stem_separated S _ (D.w++[D.sb])
  (D.c::xPiece D B) [D.b] D.properS (source_vc_address D) ha hboff
 exact (stem_separation_transport T S B [D.b] (D.c::xPiece D B) hp hsubb hsub).mpr hd

theorem external_stem_avoids_bc {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B)
 (y : Nat) (hy : y ∈ B) (hyC : y ∈ leaves D.C) (hya : y ≠ D.a) (hyb : y ≠ D.b) :
 disjointVertices (rootedSpan [y] T) (minimalVertices [D.b,D.c] T) = true := by
 have hp := agreement_block_shape T S G B h hB
 have hsuby : ∀ z, z ∈ [y] → z ∈ B := by
   intro z hz
   have he : z = y := by simpa using hz
   simpa [he] using hy
 have hsubbc : ∀ z, z ∈ [D.b,D.c] → z ∈ B := by intro z hz; simp at hz; rcases hz with hz|hz <;> subst z <;> assumption
 have hyT : y ∈ leaves T := (subtree_leaves_sublist T D.r D.C D.core).subset hyC
 have hycore := (D.coreLabels y hyT).mp hyC
 have hinside : ∀ z, z ∈ [D.b,D.c] → z ∈ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) := by
   intro z hz
   simp_all [bottom,VC,AX,leaves] <;> grind
 have hoff : ∀ z, z ∈ leaves (bottom D.sa D.sc D.sb D.a D.b D.c D.X) → z ∉ [y] := by
   intro z hz hzy
   have he : z = y := by simpa using hzy
   subst z
   simp_all [bottom,VC,AX,leaves] <;> grind
 have hd := original_subtree_stem_separated S _ D.w [D.b,D.c] [y] D.properS D.source hinside hoff
 exact (stem_separation_transport T S B [y] [D.b,D.c] hp hsuby hsubbc).mpr hd

#print axioms c_stem_avoids_xPiece
#print axioms b_stem_avoids_c_xPiece
#print axioms external_stem_avoids_bc
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping

theorem labels_mem_subtree (t : Tree) (p : RMAF.Vertex) (x : Nat) (hx : x ∈ subtreeLabels t p) :
 ∃ u, subtree t p = some u ∧ x ∈ leaves u := by
 induction p generalizing t with
 | nil => exact ⟨t,rfl,hx⟩
 | cons s p ih =>
   cases t with
   | leaf y => simp [subtreeLabels] at hx
   | node l r =>
     cases s with
     | false => exact ih l hx
     | true => exact ih r hx

theorem label_mem_rooted (t : Tree) (p : RMAF.Vertex) (x : Nat) (hx : x ∈ subtreeLabels t p) :
 p ∈ rootedSpan [x] t := by
 obtain ⟨u,hu,hx⟩ := labels_mem_subtree t p x hx
 exact rooted_subtree_root [x] t u p hu x hx (by simp)

theorem minimal_descendant (t : Tree) (P : List Nat) (p v : RMAF.Vertex)
 (hp : p ∈ minimalVertices P t) (hv : p++v ∈ rootedSpan P t) : p++v ∈ minimalVertices P t := by
 induction p generalizing t with
 | nil =>
   cases t with
   | leaf x => simpa [minimalVertices,rootedSpan] using hv
   | node l r =>
     cases hl : rootedSpan P l <;> cases hr : rootedSpan P r <;>
      simp_all [minimalVertices,rootedSpan,prependSide]
 | cons s p ih =>
   cases t with
   | leaf x => simp [minimalVertices] at hp
   | node l r =>
     cases s <;> cases hl : rootedSpan P l <;> cases hr : rootedSpan P r <;>
      simp_all [minimalVertices,rootedSpan,prependSide] <;> grind

theorem pendant_info (t : Tree) (b c : Nat) (q : RMAF.Vertex) (hq : q ∈ cuts t b c) :
 q ≠ [] ∧ q.dropLast ∈ minimalVertices [b,c] t ∧ q ∉ minimalVertices [b,c] t := by
 simpa [cuts,pendantOriginal,List.mem_filter,Bool.and_eq_true,List.isEmpty_iff,and_assoc] using (List.mem_filter.mp hq).2

theorem pendant_excludes_endpoint (t : Tree) (b c : Nat) (q : RMAF.Vertex)
 (hq : q ∈ cuts t b c) : b ∉ subtreeLabels t q ∧ c ∉ subtreeLabels t q := by
 have hi := pendant_info t b c q hq
 have hcat : q.dropLast ++ [q.getLast hi.1] = q := List.dropLast_concat_getLast hi.1
 constructor
 · intro hb
   obtain ⟨u,hu,hbu⟩ := labels_mem_subtree t q b hb
   have hr := rooted_subtree_root [b,c] t u q hu b hbu (by simp)
   have hm := minimal_descendant t [b,c] q.dropLast [q.getLast hi.1] hi.2.1 (by simpa [hcat] using hr)
   exact hi.2.2 (by simpa [hcat] using hm)
 · intro hc
   obtain ⟨u,hu,hcu⟩ := labels_mem_subtree t q c hc
   have hr := rooted_subtree_root [b,c] t u q hu c hcu (by simp)
   have hm := minimal_descendant t [b,c] q.dropLast [q.getLast hi.1] hi.2.1 (by simpa [hcat] using hr)
   exact hi.2.2 (by simpa [hcat] using hm)

theorem edge_parent_subtree (t u : Tree) (q : RMAF.Vertex) (hq : q ≠ []) (hs : subtree t q = some u) :
 ∃ s v, subtree t q.dropLast = some (orient s u v) := by
 induction q generalizing t with
 | nil => exact False.elim (hq rfl)
 | cons s p ih =>
   cases t with
   | leaf x => simp [subtree] at hs
   | node l r =>
     cases p with
     | nil =>
       cases s with
       | false =>
         have he : l = u := by simpa [subtree] using hs
         subst u
         exact ⟨false,r,by simp [subtree,orient]⟩
       | true =>
         have he : r = u := by simpa [subtree] using hs
         subst u
         exact ⟨true,l,by simp [subtree,orient]⟩
     | cons z zs =>
       cases s with
       | false => simpa [subtree] using ih l (by simp) hs
       | true => simpa [subtree] using ih r (by simp) hs

theorem pendant_crossing_parent (t : Tree) (P : List Nat) (b c : Nat) (q : RMAF.Vertex)
 (hq : q ∈ cuts t b c)
 (hc : ∃ x ∈ P, x ∈ subtreeLabels t q) (ho : ∃ y ∈ P, y ∈ leaves t ∧ y ∉ subtreeLabels t q) :
 q.dropLast ∈ minimalVertices P t := by
 obtain ⟨x,hxP,hxq⟩ := hc
 obtain ⟨y,hyP,hyt,hyq⟩ := ho
 obtain ⟨u,hu,hxu⟩ := labels_mem_subtree t q x hxq
 obtain ⟨s,v,hparent⟩ := edge_parent_subtree t u q (pendant_info t b c q hq).1 hu
 have hlabels := subtreeLabels_of_subtree t u q hu
 exact pendant_parent_crossing P t u v q.dropLast s hparent x y hxu hxP hyt hyP (by simpa [hlabels] using hyq)

theorem original_block_covered (T S : Tree) (G : List (List Nat)) (P : List Nat)
 (h : agreement T S G = true) (hP : P ∈ G) : ∀ x, x ∈ P → x ∈ leaves T := by
 have hh := h
 simp only [agreement,Bool.and_eq_true] at hh
 have hp := hh.1.1.1.1
 simp only [partitionCheck,Bool.and_eq_true] at hp
 intro x hx
 have hm := List.mem_flatten.mpr ⟨P,hP,hx⟩
 exact List.contains_iff_mem.mp (List.all_eq_true.mp hp.2 x hm)

theorem only_bc_block_can_cross_pendant (T S : Tree) (G : List (List Nat)) (B P : List Nat) (b c : Nat) (q : RMAF.Vertex)
 (h : agreement T S G = true) (hB : B ∈ G) (hP : P ∈ G) (hb : b ∈ B) (hc : c ∈ B)
 (hq : q ∈ cuts T b c)
 (hin : ∃ x ∈ P, x ∈ subtreeLabels T q) (hout : ∃ y ∈ P, y ∉ subtreeLabels T q) : P = B := by
 by_cases hne : P = B
 · exact hne
 exfalso
 have hparent := pendant_crossing_parent T P b c q hq hin (by
   obtain ⟨y,hyP,hyq⟩ := hout
   exact ⟨y,hyP,original_block_covered T S G P h hP y hyP,hyq⟩)
 have hsub : ∀ x, x ∈ [b,c] → x ∈ B := by intro x hx; simp at hx; rcases hx with hx|hx <;> subst x <;> assumption
 have hBparent := RootSpanMonotonicity.minimalVertices_mono T B [b,c] hsub q.dropLast (pendant_info T b c q hq).2.1
 have hh := h
 simp only [agreement,Bool.and_eq_true] at hh
 exact pairwise_no_common T G hh.1.2 P B hP hB hne q.dropLast hparent hBparent

#print axioms pendant_excludes_endpoint
#print axioms only_bc_block_can_cross_pendant
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping

theorem rooted_prefix (t : Tree) (P : List Nat) (p v : RMAF.Vertex)
 (h : p++v ∈ rootedSpan P t) : p ∈ rootedSpan P t := by
 induction p generalizing t with
 | nil => exact rooted_root_of_nonempty P t (by intro he; simp [he] at h)
 | cons s p ih =>
   cases t with
   | leaf x => simp [rootedSpan] at h
   | node l r =>
     cases s <;> cases hl : rootedSpan P l <;> cases hr : rootedSpan P r <;>
      simp_all [rootedSpan,prependSide] <;> grind

theorem labels_mem_leaves (t : Tree) (p : RMAF.Vertex) (x : Nat) (h : x ∈ subtreeLabels t p) : x ∈ leaves t := by
 obtain ⟨u,hu,hx⟩ := labels_mem_subtree t p x h
 exact (subtree_leaves_sublist t p u hu).subset hx

theorem same_label_addresses_comparable (t : Tree) (p q : RMAF.Vertex) (x : Nat)
 (hn : (leaves t).Nodup) (hp : x ∈ subtreeLabels t p) (hq : x ∈ subtreeLabels t q) :
 (∃ v, p++v=q) ∨ (∃ v, q++v=p) := by
 induction t generalizing p q with
 | leaf y => cases p <;> cases q <;> simp_all [subtreeLabels] <;> grind
 | node l r ihl ihr =>
   cases p with
   | nil => exact Or.inl ⟨q,rfl⟩
   | cons s p =>
     cases q with
     | nil => exact Or.inr ⟨s::p,rfl⟩
     | cons z q =>
       simp only [leaves,List.nodup_append] at hn
       cases s <;> cases z
       · rcases ihl p q hn.1 hp hq with ⟨v,hv⟩|⟨v,hv⟩
         · exact Or.inl ⟨v,by simpa using congrArg (false::·) hv⟩
         · exact Or.inr ⟨v,by simpa using congrArg (false::·) hv⟩
       · exact False.elim (hn.2.2 x (labels_mem_leaves l p x hp) x (labels_mem_leaves r q x hq) rfl)
       · exact False.elim (hn.2.2 x (labels_mem_leaves l q x hq) x (labels_mem_leaves r p x hp) rfl)
       · rcases ihr p q hn.2.1 hp hq with ⟨v,hv⟩|⟨v,hv⟩
         · exact Or.inl ⟨v,by simpa using congrArg (true::·) hv⟩
         · exact Or.inr ⟨v,by simpa using congrArg (true::·) hv⟩

theorem pendant_prefix_equal (t : Tree) (b c : Nat) (q r v : RMAF.Vertex)
 (hq : q ∈ cuts t b c) (hr : r ∈ cuts t b c) (hv : q++v=r) : q=r := by
 by_cases he : v=[]
 · simpa [he] using hv
 have hqinfo := pendant_info t b c q hq
 have hrinfo := pendant_info t b c r hr
 have hparent : r.dropLast = q++v.dropLast := by rw [←hv,List.dropLast_append_of_ne_nil he]
 have hroot : q ∈ rootedSpan [b,c] t := rooted_prefix t [b,c] q v.dropLast (by
   rw [←hparent]
   exact minimal_subset_rooted [b,c] t _ hrinfo.2.1)
 have hcat := List.dropLast_concat_getLast hqinfo.1
 have hm := minimal_descendant t [b,c] q.dropLast [q.getLast hqinfo.1] hqinfo.2.1 (by simpa [hcat] using hroot)
 exact False.elim (hqinfo.2.2 (by simpa [hcat] using hm))

theorem pendant_same_of_common_label (t : Tree) (b c : Nat) (q r : RMAF.Vertex) (x : Nat)
 (hn : (leaves t).Nodup) (hq : q ∈ cuts t b c) (hr : r ∈ cuts t b c)
 (hxq : x ∈ subtreeLabels t q) (hxr : x ∈ subtreeLabels t r) : q=r := by
 rcases same_label_addresses_comparable t q r x hn hxq hxr with ⟨v,hv⟩|⟨v,hv⟩
 · exact pendant_prefix_equal t b c q r v hq hr hv
 · exact (pendant_prefix_equal t b c r q v hr hq hv).symm

theorem cside_labels_in_X {T S : Tree} (D : LiteralGeometry T S) (q : RMAF.Vertex)
 (hq : q ∈ cSideEdges T D.b D.c) : ∀ y, y ∈ subtreeLabels T q → y ∈ leaves D.X := by
 have hf := (List.mem_filter.mp hq).2
 simp only [Bool.and_eq_true,List.contains_iff_mem,Bool.not_eq_true] at hf
 have hcut := (List.mem_filter.mp hq).1
 have hend := pendant_excludes_endpoint T D.b D.c q hcut
 have hCsep := original_subtree_stem_separated T D.C D.r (leaves D.C) [D.c] D.properT D.core
  (fun _ hx => hx) (by
   intro x hx hxc
   have he : x = D.c := by simpa using hxc
   subst x
   exact D.cC hx)
 intro y hy
 have hyT := labels_mem_leaves T q y hy
 by_cases hyX : y ∈ leaves D.X
 · exact hyX
 have hyc : y ≠ D.c := by intro he; subst y; exact hend.2 hy
 have hyC := (D.coreLabels y hyT).mpr ⟨hyX,hyc⟩
 have hm := pendant_crossing_parent T (leaves D.C) D.b D.c q hcut ⟨y,hyC,hy⟩ ⟨D.b,D.bC,(subtree_leaves_sublist T D.r D.C D.core).subset D.bC,hend.1⟩
 have hr := label_mem_rooted T q.dropLast D.c hf.1
 have hd := List.all_eq_true.mp hCsep q.dropLast hr
 simp [disjointVertices,List.contains_iff_mem,hm] at hd

theorem cside_meets_xPiece_at_most_one {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (hB : B ∈ G) (hc : D.c ∈ B)
 (q r : RMAF.Vertex) (hq : q ∈ cSideEdges T D.b D.c) (hr : r ∈ cSideEdges T D.b D.c)
 (hxq : ∃ x ∈ xPiece D B, x ∈ subtreeLabels T q)
 (hxr : ∃ x ∈ xPiece D B, x ∈ subtreeLabels T r) : q=r := by
 have hd := c_stem_avoids_xPiece D G B h hB hc
 have contained : ∀ p ∈ cSideEdges T D.b D.c,
   (∃ x ∈ xPiece D B, x ∈ subtreeLabels T p) → ∀ z ∈ xPiece D B, z ∈ subtreeLabels T p := by
   intro p hp hin z hz
   by_cases he : z ∈ subtreeLabels T p
   · exact he
   have hf := (List.mem_filter.mp hp).2
   simp only [Bool.and_eq_true,List.contains_iff_mem,Bool.not_eq_true] at hf
   have hcut := (List.mem_filter.mp hp).1
   have hm := pendant_crossing_parent T (xPiece D B) D.b D.c p hcut hin ⟨z,hz,original_block_covered T S G B h hB z (List.mem_filter.mp hz).1,he⟩
   have hroot := label_mem_rooted T p.dropLast D.c hf.1
   have hall := List.all_eq_true.mp hd p.dropLast hroot
   simp [disjointVertices,List.contains_iff_mem,hm] at hall
 obtain ⟨x,hx,hxq⟩ := hxq
 exact pendant_same_of_common_label T D.b D.c q r x D.properT
  (List.mem_filter.mp hq).1 (List.mem_filter.mp hr).1 hxq (contained r hr hxr x hx)

theorem bside_without_a_avoids_B {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B)
 (q : RMAF.Vertex) (hq : q ∈ bSideWithoutA T D.a D.b D.c) : ∀ y ∈ B, y ∉ subtreeLabels T q := by
 have hqa := (List.mem_filter.mp hq).2
 have hbs := (List.mem_filter.mp hq).1
 have hf := (List.mem_filter.mp hbs).2
 simp only [Bool.and_eq_true,List.contains_iff_mem,Bool.not_eq_true] at hf
 have hcut := (List.mem_filter.mp hbs).1
 have hend := pendant_excludes_endpoint T D.b D.c q hcut
 intro y hy hyq
 have hyT := labels_mem_leaves T q y hyq
 by_cases hyX : y ∈ leaves D.X
 · have hyPiece : y ∈ xPiece D B := List.mem_filter.mpr ⟨hy,List.contains_iff_mem.mpr hyX⟩
   have hP : D.c ∈ D.c::xPiece D B := by simp
   have hcT : D.c ∈ leaves T := (subtree_leaves_sublist T D.uc (.leaf D.c) D.leafC).subset (by simp [leaves])
   have hm := pendant_crossing_parent T (D.c::xPiece D B) D.b D.c q hcut
    ⟨y,by simp [hyPiece],hyq⟩ ⟨D.c,hP,hcT,hend.2⟩
   have hroot := label_mem_rooted T q.dropLast D.b hf.1
   have hd := List.all_eq_true.mp (b_stem_avoids_c_xPiece D G B h hB hb hc) q.dropLast hroot
   simp [disjointVertices,List.contains_iff_mem,hm] at hd
 · have hyc : y ≠ D.c := by intro he; subst y; exact hend.2 hyq
   have hyb : y ≠ D.b := by intro he; subst y; exact hend.1 hyq
   have hya : y ≠ D.a := by
     intro he; subst y
     simpa [List.contains_iff_mem,hyq] using hqa
   have hyC := (D.coreLabels y hyT).mpr ⟨hyX,hyc⟩
   have hqroot := label_mem_rooted T q y hyq
   have hqcat := List.dropLast_concat_getLast (pendant_info T D.b D.c q hcut).1
   have hroot := rooted_prefix T [y] q.dropLast [q.getLast (pendant_info T D.b D.c q hcut).1] (by simpa [hqcat] using hqroot)
   have hd := List.all_eq_true.mp (external_stem_avoids_bc D G B h hB hb hc y hy hyC hya hyb) q.dropLast hroot
   simp [disjointVertices,List.contains_iff_mem,(pendant_info T D.b D.c q hcut).2.1] at hd

#print axioms cside_labels_in_X
#print axioms cside_meets_xPiece_at_most_one
#print axioms bside_without_a_avoids_B
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping VertexGeometry

def Uniform (P : List Nat) (f : Nat → Bool) : Prop :=
 (∀ x ∈ P, f x = true) ∨ (∀ x ∈ P, f x = false)

theorem pendant_uniform_of_B_avoids (T S : Tree) (G : List (List Nat)) (B : List Nat) (b c : Nat) (q : RMAF.Vertex)
 (h : agreement T S G = true) (hB : B ∈ G) (hb : b ∈ B) (hc : c ∈ B)
 (hq : q ∈ cuts T b c) (havoid : ∀ y ∈ B, y ∉ subtreeLabels T q) :
 ∀ P ∈ G, Uniform P (subtreeLabels T q).contains := by
 intro P hP
 by_cases hin : ∃ x ∈ P, x ∈ subtreeLabels T q
 · left
   intro y hy
   by_cases hey : y ∈ subtreeLabels T q
   · exact List.contains_iff_mem.mpr hey
   · have heq := only_bc_block_can_cross_pendant T S G B P b c q h hB hP hb hc hq hin ⟨y,hy,hey⟩
     subst P
     obtain ⟨x,hx,hxq⟩ := hin
     exact False.elim (havoid x hx hxq)
 · right
   intro y hy
   have hey : y ∉ subtreeLabels T q := fun hmem => hin ⟨y,hy,hmem⟩
   simpa [List.contains_iff_mem] using hey

theorem singleton_arc_uniform {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat))
 (h : agreement T S G = true) (ha : [D.a] ∈ G) :
 ∀ P ∈ G, Uniform P (subtreeLabels T D.qa).contains := by
 have hp := h
 simp only [agreement,Bool.and_eq_true] at hp
 have hn := partition_flat_nodup _ _ hp.1.1.1.1
 have hl := subtreeLabels_of_leaf T D.qa D.a D.leafA
 intro P hP
 by_cases hpa : D.a ∈ P
 · have he := singleton_block_isolated G D.a hn ha P hP hpa
   subst P
   left
   intro x hx
   have he : x = D.a := by simpa using hx
   simp [hl,he]
 · right
   intro x hx
   have hne : x ≠ D.a := by intro he; subst x; exact hpa hx
   simp [hl,hne]

theorem refines_split (G Q : List (List Nat)) (f : Nat → Bool)
 (hn : ∀ P ∈ G, P ≠ []) (hr : Refines G Q) (hu : ∀ P ∈ G, Uniform P f) :
 Refines G (BinaryExchange.splitAll Q f) := by
 intro P hP
 obtain ⟨R,hR,hsub⟩ := hr P hP
 obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil P (hn P hP)
 rcases hu P hP with hy|hno
 · let Y := BinaryExchange.yes R f
   have hPY : ∀ y ∈ P, y ∈ Y := by intro y hyP; exact List.mem_filter.mpr ⟨hsub y hyP,hy y hyP⟩
   have hYne : Y ≠ [] := by intro he; have hh := hPY x hx; simp [he] at hh
   exact ⟨Y,List.mem_flatMap.mpr ⟨R,hR,(split_mem R Y f).mpr ⟨hYne,Or.inl rfl⟩⟩,hPY⟩
 · let Y := BinaryExchange.no R f
   have hPY : ∀ y ∈ P, y ∈ Y := by intro y hyP; exact List.mem_filter.mpr ⟨hsub y hyP,by simp [hno y hyP]⟩
   have hYne : Y ≠ [] := by intro he; have hh := hPY x hx; simp [he] at hh
   exact ⟨Y,List.mem_flatMap.mpr ⟨R,hR,(split_mem R Y f).mpr ⟨hYne,Or.inr rfl⟩⟩,hPY⟩

theorem refines_arc_from_uniform (T : Tree) (G Q : List (List Nat)) (qs : List RMAF.Vertex)
 (hn : ∀ P ∈ G, P ≠ []) (hr : Refines G Q)
 (hu : ∀ q ∈ qs, ∀ P ∈ G, Uniform P (subtreeLabels T q).contains) :
 Refines G (arcPartitionFrom T qs Q) := by
 induction qs generalizing Q with
 | nil => exact hr
 | cons q qs ih =>
   apply ih
   · exact refines_split G Q (subtreeLabels T q).contains hn hr (hu q (by simp))
   · intro r hr P hP; exact hu r (by simp [hr]) P hP

theorem agreement_refines_uniform_arc (T S : Tree) (G : List (List Nat)) (qs : List RMAF.Vertex)
 (h : agreement T S G = true)
 (hu : ∀ q ∈ qs, ∀ P ∈ G, Uniform P (subtreeLabels T q).contains) :
 Refines G (arcPartition T qs) := by
 have hp := h
 simp only [agreement,Bool.and_eq_true] at hp
 have hpart := hp.1.1.1.1
 simp only [partitionCheck,Bool.and_eq_true] at hpart
 have hn : ∀ P ∈ G, P ≠ [] := by
   intro P hP
   simpa [List.isEmpty_iff] using List.all_eq_true.mp hpart.1.1 P hP
 apply refines_arc_from_uniform T G [leaves T] qs hn ?_ hu
 intro P hP
 exact ⟨leaves T,by simp,original_block_covered T S G P h hP⟩

theorem vertices_nodup (t : Tree) : (vertices t).Nodup := by
 induction t with
 | leaf x => simp [vertices]
 | node l r ihl ihr =>
   have hl : (prependSide false (vertices l)).Nodup := List.Pairwise.map (false::·) (by
     intro a b hab he; exact hab (List.cons.inj he).2) ihl
   have hr : (prependSide true (vertices r)).Nodup := List.Pairwise.map (true::·) (by
     intro a b hab he; exact hab (List.cons.inj he).2) ihr
   apply List.nodup_cons.mpr
   constructor
   · simp [prependSide]
   · apply List.nodup_append.mpr
     refine ⟨hl,hr,?_⟩
     intro x hx y hy he
     obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
     obtain ⟨w,_,rfl⟩ := List.mem_map.mp hy
     simp at he

theorem cside_nodup (t : Tree) (b c : Nat) : (cSideEdges t b c).Nodup :=
 List.Pairwise.filter _ (List.Pairwise.filter _ (vertices_nodup t))

theorem first_two_cside_one_avoided {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (hB : B ∈ G) (hc : D.c ∈ B)
 (q r : RMAF.Vertex) (rs : List RMAF.Vertex) (hcs : cSideEdges T D.b D.c = q::r::rs) :
 (∀ y ∈ B, y ∉ subtreeLabels T q) ∨ (∀ y ∈ B, y ∉ subtreeLabels T r) := by
 have hq : q ∈ cSideEdges T D.b D.c := by simp [hcs]
 have hr : r ∈ cSideEdges T D.b D.c := by simp [hcs]
 have hn := cside_nodup T D.b D.c
 rw [hcs] at hn
 have hne : q ≠ r := by intro he; subst r; exact (List.nodup_cons.mp hn).1 (by simp)
 by_cases hin : ∃ y ∈ B, y ∈ subtreeLabels T q
 · right
   intro z hz hzr
   obtain ⟨y,hy,hyq⟩ := hin
   have hyX := cside_labels_in_X D q hq y hyq
   have hzX := cside_labels_in_X D r hr z hzr
   have he := cside_meets_xPiece_at_most_one D G B h hB hc q r hq hr
    ⟨y,List.mem_filter.mpr ⟨hy,List.contains_iff_mem.mpr hyX⟩,hyq⟩
    ⟨z,List.mem_filter.mpr ⟨hz,List.contains_iff_mem.mpr hzX⟩,hzr⟩
   exact hne he
 · left
   intro y hy hyq
   exact hin ⟨y,hy,hyq⟩

theorem typeI_one_partition_refined {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (ha : [D.a] ∈ G) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B)
 (q r : RMAF.Vertex) (rs : List RMAF.Vertex) (hcs : cSideEdges T D.b D.c = q::r::rs) :
 Refines G (arcPartition T [D.qa,q]) ∨ Refines G (arcPartition T [D.qa,r]) := by
 have hasingle := singleton_arc_uniform D G h ha
 have go : ∀ p ∈ cSideEdges T D.b D.c, (∀ y ∈ B, y ∉ subtreeLabels T p) → Refines G (arcPartition T [D.qa,p]) := by
   intro p hp hav
   apply agreement_refines_uniform_arc T S G [D.qa,p] h
   intro v hv P hP
   simp at hv
   rcases hv with he|he
   · subst v; exact hasingle P hP
   · subst v; exact pendant_uniform_of_B_avoids T S G B D.b D.c p h hB hb hc (List.mem_filter.mp hp).1 hav P hP
 rcases first_two_cside_one_avoided D G B h hB hc q r rs hcs with hq|hr
 · exact Or.inl (go q (by simp [hcs]) hq)
 · exact Or.inr (go r (by simp [hcs]) hr)

theorem typeII_nonempty_partition_refined {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (ha : [D.a] ∈ G) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B) :
 Refines G (arcPartition T (D.qa :: bSideWithoutA T D.a D.b D.c)) := by
 apply agreement_refines_uniform_arc T S G _ h
 intro q hq P hP
 rcases List.mem_cons.mp hq with he|hq
 · subst q; exact singleton_arc_uniform D G h ha P hP
 · have hcut := (List.mem_filter.mp (List.mem_filter.mp hq).1).1
   exact pendant_uniform_of_B_avoids T S G B D.b D.c q h hB hb hc hcut (bside_without_a_avoids_B D G B h hB hb hc q hq) P hP

#print axioms typeI_one_partition_refined
#print axioms typeII_nonempty_partition_refined
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping VertexGeometry

theorem vertex_subtree_exists (t : Tree) (q : RMAF.Vertex) (hq : q ∈ vertices t) : ∃ u, subtree t q = some u := by
 induction t generalizing q with
 | leaf x =>
   have he : q=[] := by simpa [vertices] using hq
   subst q
   exact ⟨.leaf x,rfl⟩
 | node l r ihl ihr =>
   cases q with
   | nil => exact ⟨.node l r,rfl⟩
   | cons s p =>
     cases s with
     | false =>
       have hp : p ∈ vertices l := by simpa [vertices,prependSide] using hq
       exact ihl p hp
     | true =>
       have hp : p ∈ vertices r := by simpa [vertices,prependSide] using hq
       exact ihr p hp

theorem two_disjoint_arcs_guard (T S U : Tree) (a b : Nat) (qa q : RMAF.Vertex)
 (hn : (leaves T).Nodup) (ha : subtree T qa = some (.leaf a)) (hq : subtree T q = some U)
 (hqne : q ≠ []) (hau : a ∉ leaves U) (hbT : b ∈ leaves T) (hba : b ≠ a) (hbu : b ∉ leaves U) :
 currentGuard T S (targetBranch T [qa,q]) = true := by
 have halabel : subtreeLabels T qa = [a] := subtreeLabels_of_subtree T (.leaf a) qa ha
 have hqlabel : subtreeLabels T q = leaves U := subtreeLabels_of_subtree T U q hq
 have hqane : qa ≠ [] := by
   intro he
   subst qa
   have heT : T = .leaf a := by simpa [subtree] using ha
   subst T
   have he : b = a := by simpa [leaves] using hbT
   exact hba he
 have hneq : qa ≠ q := by
   intro he
   have hm : a ∈ subtreeLabels T q := by rw [←he,halabel]; simp
   exact hau (by simpa [hqlabel] using hm)
 let R := (leaves T).filter (fun x => !(([a]++leaves U).contains x))
 have hRne : R ≠ [] := by
   have hbR : b ∈ R := by simp [R,hbT,hba,hbu]
   intro he
   simp [he] at hbR
 have hya : (leaves T).filter [a].contains = [a] := by
   simpa [leaves] using filter_leaves_subtree T (.leaf a) qa hn ha
 have hyu := filter_leaves_subtree T U q hn hq
 have hdis : ∀ x ∈ [a], x ∉ leaves U := by
   intro x hx
   have he : x=a := by simpa using hx
   simpa [he] using hau
 have hpart := mask_partition_check (leaves T) [a] (leaves U) hn hya hyu hdis (by simp) (leaves_nonempty U) hRne
 have hpartR : partitionCheck (leaves T) [[a],leaves U,R] = true := by simpa only [R] using hpart
 have harc : arcPartition T [qa,q] = [[a],leaves U,R] := by
   have he := split_two_masks (leaves T) [a] (leaves U) hya hyu hdis (by simp) (leaves_nonempty U) hRne
   simpa [arcPartition,arcPartitionFrom,splitForest,halabel,hqlabel,R] using he
 have hoffA : ∀ x ∈ leaves (.leaf a), x ∉ R := by
   intro x hx hxr
   have he : x=a := by simpa [leaves] using hx
   subst x
   simp [R] at hxr
 have hoffU : ∀ x ∈ leaves U, x ∉ R := by
   intro x hx hxr
   simp [R,hx] at hxr
 have hdAU := subtree_mask_disjoint T (.leaf a) qa hn ha (leaves U) (by simpa [leaves] using hdis)
 have hdAR := subtree_mask_disjoint T (.leaf a) qa hn ha R hoffA
 have hdUR := subtree_mask_disjoint T U q hn hq R hoffU
 have hemb : pairwiseEmbeddings T [[a],leaves U,R] = true := by
   simpa [pairwiseEmbeddings,leaves] using And.intro (And.intro hdAU hdAR) hdUR
 simp [currentGuard,current,targetBranch,paid,harc,hpartR,hemb,hqane,hqne,hneq,ha,hq]

theorem cside_target_guard {T S : Tree} (D : LiteralGeometry T S) (q : RMAF.Vertex)
 (hq : q ∈ cSideEdges T D.b D.c) : currentGuard T S (targetBranch T [D.qa,q]) = true := by
 have hcut := (List.mem_filter.mp hq).1
 have hvertex := (List.mem_filter.mp hcut).1
 obtain ⟨U,hU⟩ := vertex_subtree_exists T q hvertex
 have hlabels := subtreeLabels_of_subtree T U q hU
 have hend := pendant_excludes_endpoint T D.b D.c q hcut
 have hsep := source_label_separation D
 have haoff : D.a ∉ leaves U := by
   intro haU
   have haX := cside_labels_in_X D q hq D.a (by simpa [hlabels] using haU)
   exact hsep.2.2.2.1 haX
 have hbT := (subtree_leaves_sublist T D.r D.C D.core).subset D.bC
 apply two_disjoint_arcs_guard T S U D.a D.b D.qa q D.properT D.leafA hU
  (pendant_info T D.b D.c q hcut).1 haoff hbT (Ne.symm hsep.1)
 exact fun hbU => hend.1 (by simpa [hlabels] using hbU)

theorem exceptional_typeI_actual_target {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (ha : [D.a] ∈ G) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B)
 (q r : RMAF.Vertex) (rs : List RMAF.Vertex) (hcs : cSideEdges T D.b D.c = q::r::rs) :
 ∃ child ∈ guardedPlan D, Refines G child.partition := by
 have go : ∀ p ∈ [q,r], Refines G (arcPartition T [D.qa,p]) →
  ∃ child ∈ guardedPlan D, Refines G child.partition := by
   intro p hp href
   have hpC : p ∈ cSideEdges T D.b D.c := by simp at hp; simp [hcs]; grind
   refine ⟨targetBranch T [D.qa,p],List.mem_filter.mpr ⟨?_,cside_target_guard D p hpC⟩,href⟩
   simp [literalPlan,rawPlan,hcs,typeIBranches]
   simp at hp
   rcases hp with hp|hp <;> subst p <;> simp
 rcases typeI_one_partition_refined D G B h ha hB hb hc q r rs hcs with hq|hr
 · exact go q (by simp) hq
 · exact go r (by simp) hr

#print axioms two_disjoint_arcs_guard
#print axioms cside_target_guard
#print axioms exceptional_typeI_actual_target
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping VertexGeometry

theorem lca_branch (t : Tree) (ub uc : RMAF.Vertex) (b c : Nat)
 (hb : LeafAt t ub b) (hc : LeafAt t uc c) (hbc : b ≠ c) :
 ∃ A C s, subtree t (lca ub uc) = some (orient s A C) ∧ b ∈ leaves A ∧ c ∈ leaves C := by
 induction ub generalizing t uc with
 | nil =>
   have he : t = .leaf b := by simpa [LeafAt,subtree] using hb
   subst t
   have hcmem : c ∈ leaves (.leaf b) := (subtree_leaves_sublist (.leaf b) uc (.leaf c) hc).subset (by simp [leaves])
   have he : c=b := by simpa [leaves] using hcmem
   exact False.elim (hbc he.symm)
 | cons u ub ih =>
   cases t with
   | leaf x => simp [LeafAt,subtree] at hb
   | node l r =>
     cases uc with
     | nil => simp [LeafAt,subtree] at hc
     | cons v uc =>
       cases u <;> cases v
       · obtain ⟨A,C,s,hs,hbA,hcC⟩ := ih l uc hb hc
         exact ⟨A,C,s,hs,hbA,hcC⟩
       · exact ⟨l,r,false,rfl,(subtree_leaves_sublist l ub (.leaf b) hb).subset (by simp [leaves]),(subtree_leaves_sublist r uc (.leaf c) hc).subset (by simp [leaves])⟩
       · exact ⟨r,l,true,rfl,(subtree_leaves_sublist r ub (.leaf b) hb).subset (by simp [leaves]),(subtree_leaves_sublist l uc (.leaf c) hc).subset (by simp [leaves])⟩
       · obtain ⟨A,C,s,hs,hbA,hcC⟩ := ih r uc hb hc
         exact ⟨A,C,s,hs,hbA,hcC⟩

theorem literal_lca_subtree {T S : Tree} (D : LiteralGeometry T S) :
 ∃ U, subtree T (lca D.ub D.uc) = some U ∧ D.b ∈ leaves U ∧ D.c ∈ leaves U ∧
  lca D.ub D.uc ∈ minimalVertices [D.b,D.c] T := by
 have hbc := (source_label_separation D).2.2.1
 obtain ⟨A,C,s,hs,hbA,hcC⟩ := lca_branch T D.ub D.uc D.b D.c D.leafB D.leafC hbc
 have hbU : D.b ∈ leaves (orient s A C) := by simp [hbA]
 have hcU : D.c ∈ leaves (orient s A C) := by simp [hcC]
 have hm := (orient_minimal_bridge [D.b,D.c] A C s D.b D.c hbA hcC (by simp) (by simp)).1
 have hlift := minimal_subtree_lift [D.b,D.c] T _ (lca D.ub D.uc) [] hs hm
 exact ⟨orient s A C,hs,hbU,hcU,by simpa using hlift⟩

theorem bc_block_inside_lca {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B) :
 ∀ y ∈ B, y ∈ subtreeLabels T (lca D.ub D.uc) := by
 obtain ⟨U,hU,hbU,hcU,hqmin⟩ := literal_lca_subtree D
 have hlabels := subtreeLabels_of_subtree T U (lca D.ub D.uc) hU
 have hqb : lca D.ub D.uc ∈ rootedSpan [D.b] T := rooted_subtree_root [D.b] T U _ hU D.b hbU (by simp)
 have hqc : lca D.ub D.uc ∈ rootedSpan [D.c] T := rooted_subtree_root [D.c] T U _ hU D.c hcU (by simp)
 have hcoreSep := original_subtree_stem_separated T D.C D.r (leaves D.C) [D.c] D.properT D.core (fun _ hx => hx) (by
   intro x hx hxc
   have he : x=D.c := by simpa using hxc
   subst x
   exact D.cC hx)
 have hCinside : ∀ y ∈ leaves D.C, y ∈ leaves U := by
   intro y hyC
   by_cases hyU : y ∈ leaves U
   · exact hyU
   have hyT := (subtree_leaves_sublist T D.r D.C D.core).subset hyC
   have hm := subtree_root_crossing (leaves D.C) T U (lca D.ub D.uc) hU D.b y hbU D.bC hyT hyC hyU
   have hd := List.all_eq_true.mp hcoreSep _ hqc
   simp [disjointVertices,List.contains_iff_mem,hm] at hd
 intro y hyB
 rw [hlabels]
 by_cases hyU : y ∈ leaves U
 · exact hyU
 have hyT := original_block_covered T S G B h hB y hyB
 by_cases hyX : y ∈ leaves D.X
 · have hyPiece : y ∈ xPiece D B := List.mem_filter.mpr ⟨hyB,List.contains_iff_mem.mpr hyX⟩
   have hm := subtree_root_crossing (D.c::xPiece D B) T U (lca D.ub D.uc) hU D.c y hcU (by simp) hyT (by simp [hyPiece]) hyU
   have hd := List.all_eq_true.mp (b_stem_avoids_c_xPiece D G B h hB hb hc) _ hqb
   simp [disjointVertices,List.contains_iff_mem,hm] at hd
 · have hyc : y ≠ D.c := by intro he; subst y; exact hyU hcU
   exact hCinside y ((D.coreLabels y hyT).mpr ⟨hyX,hyc⟩)

theorem lca_arc_uniform {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B) :
 ∀ P ∈ G, Uniform P (subtreeLabels T (lca D.ub D.uc)).contains := by
 have hBin := bc_block_inside_lca D G B h hB hb hc
 obtain ⟨U,hU,hbU,hcU,hqmin⟩ := literal_lca_subtree D
 have hlabels := subtreeLabels_of_subtree T U (lca D.ub D.uc) hU
 have hsub : ∀ x, x ∈ [D.b,D.c] → x ∈ B := by intro x hx; simp at hx; rcases hx with hx|hx <;> subst x <;> assumption
 have hqB := RootSpanMonotonicity.minimalVertices_mono T B [D.b,D.c] hsub _ hqmin
 have hp := h
 simp only [agreement,Bool.and_eq_true] at hp
 intro P hP
 by_cases hin : ∃ x ∈ P, x ∈ leaves U
 · left
   intro y hyP
   by_cases hyU : y ∈ leaves U
   · simpa [hlabels] using List.contains_iff_mem.mpr hyU
   · obtain ⟨x,hxP,hxU⟩ := hin
     have hm := subtree_root_crossing P T U (lca D.ub D.uc) hU x y hxU hxP (original_block_covered T S G P h hP y hyP) hyP hyU
     have hne : P ≠ B := by
       intro he
       subst P
       exact hyU (by simpa [hlabels] using hBin y hyP)
     exact False.elim (pairwise_no_common T G hp.1.2 P B hP hB hne _ hm hqB)
 · right
   intro y hyP
   have hyU : y ∉ leaves U := fun hyU => hin ⟨y,hyP,hyU⟩
   simpa [hlabels,List.contains_iff_mem] using hyU

theorem fallback_partition_refined {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (ha : [D.a] ∈ G) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B) :
 Refines G (arcPartition T [D.qa,lca D.ub D.uc]) := by
 apply agreement_refines_uniform_arc T S G _ h
 intro q hq P hP
 simp at hq
 rcases hq with he|he
 · subst q; exact singleton_arc_uniform D G h ha P hP
 · subst q; exact lca_arc_uniform D G B h hB hb hc P hP

#print axioms bc_block_inside_lca
#print axioms fallback_partition_refined
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping VertexGeometry

theorem exceptional_raw_target {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (ha : [D.a] ∈ G) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B) :
 ∃ child ∈ literalPlan D, child.role = .target ∧ Refines G child.partition := by
 have noI : (cSideEdges T D.b D.c).length < 2 →
  ∃ child ∈ literalPlan D, child.role = .target ∧ Refines G child.partition := by
   intro hsmall
   have hraw : literalPlan D = match bSideWithoutA T D.a D.b D.c with
    | [] => typeIIBranches T S D.a D.b D.qa (bArc D.w D.sb) [lca D.ub D.uc]
    | qs => typeIIBranches T S D.a D.b D.qa (bArc D.w D.sb) qs := by
     cases hcs : cSideEdges T D.b D.c with
     | nil => simp only [literalPlan,rawPlan,hcs] <;> rfl
     | cons q qs =>
       cases qs with
       | nil => simp only [literalPlan,rawPlan,hcs] <;> rfl
       | cons r rs => simp [hcs] at hsmall; omega
   cases hbs : bSideWithoutA T D.a D.b D.c with
   | nil =>
     refine ⟨targetBranch T [D.qa,lca D.ub D.uc],?_,rfl,fallback_partition_refined D G B h ha hB hb hc⟩
     simp [hraw,hbs,typeIIBranches]
   | cons q qs =>
     refine ⟨targetBranch T (D.qa::q::qs),?_,rfl,?_⟩
     · simp [hraw,hbs,typeIIBranches]
     · simpa [hbs,targetBranch] using typeII_nonempty_partition_refined D G B h ha hB hb hc
 cases hcs : cSideEdges T D.b D.c with
 | nil => exact noI (by simp [hcs])
 | cons q qs =>
   cases qs with
   | nil => exact noI (by simp [hcs])
   | cons r rs =>
     have go : ∀ p ∈ [q,r], Refines G (arcPartition T [D.qa,p]) →
      ∃ child ∈ literalPlan D, child.role = .target ∧ Refines G child.partition := by
       intro p hp href
       refine ⟨targetBranch T [D.qa,p],?_,rfl,href⟩
       simp at hp
       rcases hp with hp|hp <;> subst p <;> simp [literalPlan,rawPlan,hcs,typeIBranches]
     rcases typeI_one_partition_refined D G B h ha hB hb hc q r rs hcs with hq|hr
     · exact go q (by simp) hq
     · exact go r (by simp) hr

theorem exceptional_typeI_G0 {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (ha : [D.a] ∈ G) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B)
 (q r : RMAF.Vertex) (rs : List RMAF.Vertex) (hcs : cSideEdges T D.b D.c = q::r::rs) :
 ∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧ H.length ≤ G.length ∧ Refines H child.partition := by
 obtain ⟨child,hchild,href⟩ := exceptional_typeI_actual_target D G B h ha hB hb hc q r rs hcs
 exact ⟨child,hchild,G,h,Nat.le_refl _,href⟩

-- Exact requested target type; ExceptionalTarget.lean supplies its proof.
def ExceptionalTargetGoal : Prop :=
 ∀ (T S : Tree) (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat),
  agreement T S G = true → [D.a] ∈ G → B ∈ G → D.b ∈ B → D.c ∈ B →
  (∃ x ∈ B, x ∈ leaves D.X) →
  ∃ child ∈ guardedPlan D, Refines G child.partition

#print axioms exceptional_raw_target
#print axioms exceptional_typeI_G0
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping VertexGeometry BinaryExchange

def Cross (P : List Nat) (f : Nat → Bool) : Prop := yes P f ≠ [] ∧ no P f ≠ []

theorem split_length_cross (P : List Nat) (f : Nat → Bool) (h : Cross P f) : (split P f).length = 2 := by
 cases hy : yes P f <;> cases hn : no P f <;> simp_all [Cross,split]

theorem split_length_nocross (P : List Nat) (f : Nat → Bool) (hp : P ≠ []) (h : ¬ Cross P f) :
 (split P f).length = 1 := by
 have he : (yes P f).length + (no P f).length = P.length := by
   simpa [yes,no] using (List.filter_append_perm f P).length_eq
 cases hy : yes P f <;> cases hn : no P f
 · have hz : P.length=0 := by simpa [hy,hn] using he.symm
   exact False.elim (hp (List.length_eq_zero_iff.mp hz))
 · simp [split,hy,hn]
 · simp [split,hy,hn]
 · exact False.elim (h ⟨by simp [hy],by simp [hn]⟩)

theorem splitAll_length_nocross (F : List (List Nat)) (f : Nat → Bool)
 (hn : ∀ P ∈ F, P ≠ []) (hc : ∀ P ∈ F, ¬ Cross P f) : (splitAll F f).length = F.length := by
 induction F with
 | nil => simp [splitAll]
 | cons P F ih =>
   have hp := split_length_nocross P f (hn P (by simp)) (hc P (by simp))
   have ht := ih (fun Q hQ => hn Q (by simp [hQ])) (fun Q hQ => hc Q (by simp [hQ]))
   change (split P f ++ splitAll F f).length = (P::F).length
   rw [List.length_append,hp,ht]
   simp [Nat.add_comm]

theorem splitAll_length_one_cross (F : List (List Nat)) (f : Nat → Bool) (R : List Nat)
 (hnd : F.Nodup) (hn : ∀ P ∈ F, P ≠ []) (hR : R ∈ F) (hcross : Cross R f)
 (hunique : ∀ P ∈ F, Cross P f → P=R) : (splitAll F f).length = F.length+1 := by
 induction F generalizing R with
 | nil => simp at hR
 | cons P F ih =>
   have hndF := (List.nodup_cons.mp hnd).2
   have hnF : ∀ Q ∈ F, Q ≠ [] := fun Q hQ => hn Q (by simp [hQ])
   by_cases he : P=R
   · subst P
     have hnot : R ∉ F := (List.nodup_cons.mp hnd).1
     have hnc : ∀ Q ∈ F, ¬ Cross Q f := by
       intro Q hQ hQcross
       have he := hunique Q (by simp [hQ]) hQcross
       subst Q
       exact hnot hQ
     have ht := splitAll_length_nocross F f hnF hnc
     have hp := split_length_cross R f hcross
     simp [splitAll,List.flatMap_cons,hp] at *
     omega
   · have hRin : R ∈ F := (List.mem_cons.mp hR).resolve_left (Ne.symm he)
     have hnc : ¬ Cross P f := fun hc => he (hunique P (by simp) hc)
     have hp := split_length_nocross P f (hn P (by simp)) hnc
     have ht := ih R hndF hnF hRin hcross (fun Q hQ => hunique Q (by simp [hQ]))
     simp [splitAll,List.flatMap_cons,hp] at *
     omega

theorem blocks_nodup (L : List Nat) (F : List (List Nat)) (h : partitionCheck L F = true) : F.Nodup := by
 have hf := partition_flat_nodup L F h
 have hh := h
 simp only [partitionCheck,Bool.and_eq_true] at hh
 have hne : ∀ P ∈ F, P ≠ [] := by
   intro P hP; simpa [List.isEmpty_iff] using List.all_eq_true.mp hh.1.1 P hP
 clear hh h
 induction F with
 | nil => simp
 | cons P F ih =>
   simp only [List.flatten_cons,List.nodup_append] at hf
   apply List.nodup_cons.mpr
   constructor
   · intro hP
     obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil P (hne P (by simp))
     exact hf.2.2 x hx x (List.mem_flatten.mpr ⟨P,hP,hx⟩) rfl
   · exact ih hf.2.1 (fun Q hQ => hne Q (by simp [hQ]))

theorem cross_has_labels (P : List Nat) (Y : List Nat) (h : Cross P Y.contains) :
 (∃ x ∈ P, x ∈ Y) ∧ (∃ y ∈ P, y ∉ Y) := by
 obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (yes P Y.contains) h.1
 obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil (no P Y.contains) h.2
 have hxf := List.mem_filter.mp hx
 have hyf := List.mem_filter.mp hy
 exact ⟨⟨x,hxf.1,List.contains_iff_mem.mp hxf.2⟩,⟨y,hyf.1,by simpa [List.contains_iff_mem] using hyf.2⟩⟩

theorem pendant_family_count (T : Tree) (b c : Nat) (F : List (List Nat)) (R : List Nat) (qs : List RMAF.Vertex)
 (hnT : (leaves T).Nodup) (hAF : agreement T T F = true) (hR : R ∈ F) (hb : b ∈ R) (hc : c ∈ R)
 (hqs : qs.Nodup) (hcuts : ∀ q ∈ qs, q ∈ cuts T b c)
 (hinside : ∀ q ∈ qs, ∀ x ∈ subtreeLabels T q, x ∈ R) :
 (arcPartitionFrom T qs F).length = F.length + qs.length := by
 induction qs generalizing F R with
 | nil => simp [arcPartitionFrom]
 | cons q qs ih =>
   have hcut := hcuts q (by simp)
   obtain ⟨U,hU⟩ := vertex_subtree_exists T q (List.mem_filter.mp hcut).1
   have hlabels := subtreeLabels_of_subtree T U q hU
   let f := (subtreeLabels T q).contains
   let F' := splitAll F f
   let R' := no R f
   have hend := pendant_excludes_endpoint T b c q hcut
   have hbR' : b ∈ R' := List.mem_filter.mpr ⟨hb,by simp [f,hend.1]⟩
   have hcR' : c ∈ R' := List.mem_filter.mpr ⟨hc,by simp [f,hend.2]⟩
   have hRne : R' ≠ [] := by intro he; have hh := hbR'; simp [he] at hh
   have hRin : R' ∈ F' := List.mem_flatMap.mpr ⟨R,hR,(split_mem R R' f).mpr ⟨hRne,Or.inr rfl⟩⟩
   have hAF' : agreement T T F' = true := by
     simpa [F',f,hlabels] using agreement_original_target_edge T T U F q hnT hnT hAF hU
   have hnewinside : ∀ r ∈ qs, ∀ x ∈ subtreeLabels T r, x ∈ R' := by
     intro r hr x hx
     have hxR := hinside r (by simp [hr]) x hx
     have hxoff : x ∉ subtreeLabels T q := by
       intro hxq
       have he := pendant_same_of_common_label T b c q r x hnT hcut (hcuts r (by simp [hr])) hxq hx
       subst r
       exact (List.nodup_cons.mp hqs).1 hr
     exact List.mem_filter.mpr ⟨hxR,by simp [f,hxoff]⟩
   have hcross : Cross R f := by
     obtain ⟨x,hxU⟩ := List.exists_mem_of_ne_nil (leaves U) (leaves_nonempty U)
     have hxq : x ∈ subtreeLabels T q := by simpa [hlabels] using hxU
     have hxR := hinside q (by simp) x hxq
     constructor
     · intro he
       have hh : x ∈ yes R f := List.mem_filter.mpr ⟨hxR,by simp [f,hxq]⟩
       simp [he] at hh
     · exact hRne
   have hp := hAF
   simp only [agreement,Bool.and_eq_true] at hp
   have hpart := hp.1.1.1.1
   have hnF : ∀ P ∈ F, P ≠ [] := by
     have hh := hpart
     simp only [partitionCheck,Bool.and_eq_true] at hh
     intro P hP; simpa [List.isEmpty_iff] using List.all_eq_true.mp hh.1.1 P hP
   have hunique : ∀ P ∈ F, Cross P f → P=R := by
     intro P hP hPcross
     have hx := cross_has_labels P (subtreeLabels T q) hPcross
     exact only_bc_block_can_cross_pendant T T F R P b c q hAF hR hP hb hc hcut hx.1 hx.2
   have hlen := splitAll_length_one_cross F f R (blocks_nodup _ _ hpart) hnF hR hcross hunique
   have ht := ih F' R' hAF' hRin hbR' hcR' (List.nodup_cons.mp hqs).2
    (fun r hr => hcuts r (by simp [hr])) hnewinside
   change (arcPartitionFrom T qs F').length = F.length + (q::qs).length
   rw [ht]
   change (splitAll F f).length + qs.length = _
   rw [hlen]
   simp only [List.length_cons]
   omega

#print axioms pendant_family_count
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping VertexGeometry BinaryExchange

theorem sameShape_self (t : Tree) : sameShape t t = true := by
 induction t with
 | leaf x => simp [sameShape]
 | node l r ihl ihr => simp [sameShape,ihl,ihr]

theorem restrict_all (t : Tree) (P : List Nat) (h : ∀ x ∈ leaves t, x ∈ P) : restrict P t = some t := by
 induction t with
 | leaf x => simp [restrict,h x (by simp [leaves])]
 | node l r ihl ihr =>
   have hl := ihl (fun x hx => h x (List.mem_append_left _ hx))
   have hr := ihr (fun x hx => h x (List.mem_append_right _ hx))
   simp [restrict,hl,hr]

theorem one_partition_check (L : List Nat) (hn : L.Nodup) (hne : L ≠ []) : partitionCheck L [L] = true := by
 simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
 refine ⟨⟨?_,?_⟩,?_⟩
 · intro P hP
   have he : P=L := by simpa using hP
   subst P
   simpa [List.isEmpty_iff] using hne
 · intro x hx
   simpa using beq_iff_eq.mpr (hn.count_of_mem hx)
 · intro x hx
   exact List.contains_iff_mem.mpr (by simpa using hx)

theorem agreement_self_one (T : Tree) (hn : (leaves T).Nodup) : agreement T T [leaves T] = true := by
 have hp := one_partition_check (leaves T) hn (leaves_nonempty T)
 have hr := restrict_all T (leaves T) (fun _ hx => hx)
 simp [agreement,hp,restrictionAgrees,hr,sameShape_self,pairwiseEmbeddings]

theorem agreement_arc_from (T : Tree) (F : List (List Nat)) (qs : List RMAF.Vertex)
 (hn : (leaves T).Nodup) (hAF : agreement T T F = true)
 (hv : ∀ q ∈ qs, q ∈ vertices T) : agreement T T (arcPartitionFrom T qs F) = true := by
 induction qs generalizing F with
 | nil => exact hAF
 | cons q qs ih =>
   obtain ⟨U,hU⟩ := vertex_subtree_exists T q (hv q (by simp))
   have hlabels := subtreeLabels_of_subtree T U q hU
   apply ih
   · simpa [splitForest,hlabels] using agreement_original_target_edge T T U F q hn hn hAF hU
   · intro r hr; exact hv r (by simp [hr])

theorem bside_nodup (t : Tree) (a b c : Nat) : (bSideWithoutA t a b c).Nodup :=
 List.Pairwise.filter _ (List.Pairwise.filter _ (List.Pairwise.filter _ (vertices_nodup t)))

theorem literal_typeII_target_guard {T S : Tree} (D : LiteralGeometry T S) :
 currentGuard T S (targetBranch T (D.qa :: bSideWithoutA T D.a D.b D.c)) = true := by
 let qs := bSideWithoutA T D.a D.b D.c
 let R := (leaves T).filter (fun x => x != D.a)
 let F := singletonPartition T D.a
 have hsep := source_label_separation D
 have hbT : D.b ∈ leaves T := (subtree_leaves_sublist T D.r D.C D.core).subset D.bC
 have hcT : D.c ∈ leaves T := (subtree_leaves_sublist T D.uc (.leaf D.c) D.leafC).subset (by simp [leaves])
 have hbR : D.b ∈ R := by simp [R,hbT,Ne.symm hsep.1]
 have hcR : D.c ∈ R := by simp [R,hcT,Ne.symm hsep.2.1]
 have hRne : R ≠ [] := by intro he; have hh := hbR; simp [he] at hh
 have hstart := singleton_arc_partition T D.qa D.a D.properT D.leafA hRne
 have hqaroot : D.qa ≠ [] := by
   intro he
   have heT : T = .leaf D.a := by simpa [he,LeafAt,subtree] using D.leafA
   have heba : D.b=D.a := by simpa [heT,leaves] using hbT
   exact hsep.1 heba.symm
 have hqvalid : ∀ q ∈ qs, q ∈ cuts T D.b D.c := by
   intro q hq
   exact (List.mem_filter.mp (List.mem_filter.mp hq).1).1
 have hqvertex : ∀ q ∈ qs, q ∈ vertices T := by intro q hq; exact (List.mem_filter.mp (hqvalid q hq)).1
 have hqoffa : ∀ q ∈ qs, D.a ∉ subtreeLabels T q := by
   intro q hq
   simpa [List.contains_iff_mem] using (List.mem_filter.mp hq).2
 have hqaLabel := subtreeLabels_of_leaf T D.qa D.a D.leafA
 have hqand : D.qa ∉ qs := by
   intro hm
   exact hqoffa D.qa hm (by simp [hqaLabel])
 have hnd : (D.qa::qs).Nodup := List.nodup_cons.mpr ⟨hqand,bside_nodup T D.a D.b D.c⟩
 have hv : ∀ q ∈ D.qa::qs, q ∈ vertices T := by
   intro q hq
   rcases List.mem_cons.mp hq with he|hq
   · subst q; exact subtree_vertex T (.leaf D.a) D.qa D.leafA
   · exact hqvertex q hq
 have hAF : agreement T T (arcPartition T (D.qa::qs)) = true := agreement_arc_from T [leaves T] (D.qa::qs) D.properT (agreement_self_one T D.properT) hv
 have hAFstart : agreement T T F = true := by
   change agreement T T (singletonPartition T D.a) = true
   rw [←hstart]
   exact agreement_arc_from T [leaves T] [D.qa] D.properT (agreement_self_one T D.properT) (by
     intro q hq
     have he : q=D.qa := by simpa using hq
     subst q
     exact subtree_vertex T (.leaf D.a) D.qa D.leafA)
 have hRin : R ∈ F := by simp [F,singletonPartition,R]
 have hinside : ∀ q ∈ qs, ∀ x ∈ subtreeLabels T q, x ∈ R := by
   intro q hq x hx
   have hxT := labels_mem_leaves T q x hx
   have hxa : x ≠ D.a := by intro he; subst x; exact hqoffa q hq hx
   simp [R,hxT,hxa]
 have hlen := pendant_family_count T D.b D.c F R qs D.properT hAFstart hRin hbR hcR (bside_nodup T D.a D.b D.c) hqvalid hinside
 have harc : arcPartition T (D.qa::qs) = arcPartitionFrom T qs F := by
   change arcPartitionFrom T qs (splitForest [leaves T] (subtreeLabels T D.qa)) = _
   have he : splitForest [leaves T] (subtreeLabels T D.qa) = F := by
     simpa [arcPartition,arcPartitionFrom] using hstart
   rw [he]
 have hcount : (arcPartition T (D.qa::qs)).length = (D.qa::qs).length+1 := by
   rw [harc,hlen]
   simp [F,singletonPartition]
   omega
 have hh := hAF
 simp only [agreement,Bool.and_eq_true] at hh
 have hpart := hh.1.1.1.1
 have hemb := hh.1.2
 have hall : (D.qa::qs).all (fun q => !q.isEmpty && (subtree T q).isSome) = true := by
   apply List.all_eq_true.mpr
   intro q hq
   rcases List.mem_cons.mp hq with he|hq
   · subst q
     have he : subtree T D.qa = some (.leaf D.a) := D.leafA
     simp [hqaroot,he]
   · obtain ⟨U,hU⟩ := vertex_subtree_exists T q (hqvertex q hq)
     simp [(pendant_info T D.b D.c q (hqvalid q hq)).1,hU]
 simpa only [qs] using (show currentGuard T S (targetBranch T (D.qa::qs)) = true from by
   simp [currentGuard,current,targetBranch,paid,hnd,hall,hpart,hemb,hcount])

#print axioms literal_typeII_target_guard
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping VertexGeometry BinaryExchange

theorem orient_nodup_parts (L R : Tree) (s : Bool) (hn : (leaves (orient s L R)).Nodup) :
 (leaves L).Nodup ∧ (leaves R).Nodup ∧ (∀ x ∈ leaves L, x ∉ leaves R) := by
 cases s <;> simp_all [orient,leaves,List.nodup_append] <;> grind

theorem cherry_orient_iff (L R : Tree) (s : Bool) (a b : Nat) :
 ActualCherry (orient s L R) a b ↔
 (L=.leaf a ∧ R=.leaf b) ∨ (L=.leaf b ∧ R=.leaf a) ∨ ActualCherry L a b ∨ ActualCherry R a b := by
 cases s <;> simp [orient,actual_cherry_node_iff] <;> grind

theorem bside_off_child (T A B R : Tree) (s z : Bool) (a b c : Nat)
 (hT : T=orient s (orient z A B) R) (hbA : b ∈ leaves A) (hcR : c ∈ leaves R)
 (haB : a ∉ leaves B) (hbB : b ∉ leaves B) (hcL : c ∉ leaves (orient z A B)) :
 [s,!z] ∈ bSideWithoutA T a b c := by
 have hbL : b ∈ leaves (orient z A B) := by simp [hbA]
 have hparent : subtree T [s] = some (orient z A B) := by rw [hT]; cases s <;> simp [orient,subtree]
 have hchild : subtree T [s,!z] = some B := by rw [hT]; cases s <;> cases z <;> simp [orient,subtree]
 have hlabelsP := subtreeLabels_of_subtree T (orient z A B) [s] hparent
 have hlabelsQ := subtreeLabels_of_subtree T B [s,!z] hchild
 have hrootL := rooted_root_of_selected [b,c] (orient z A B) b hbL (by simp)
 have hmP : [s] ∈ minimalVertices [b,c] T := by
   rw [hT]
   simpa using (orient_minimal_bridge [b,c] (orient z A B) R s b c hbL hcR (by simp) (by simp)).2 [] hrootL
 have hcB : c ∉ leaves B := by intro hc; exact hcL (by simp [hc])
 have hempty : rootedSpan [b,c] B = [] := rooted_empty_of_disjoint [b,c] B (by
   intro x hx hp
   simp at hp
   rcases hp with he|he <;> subst x <;> contradiction)
 have hnot : [s,!z] ∉ minimalVertices [b,c] T := by
   intro hm
   have hr := minimal_subset_rooted [b,c] T _ hm
   have ht := rooted_trace_subtree [b,c] T B [s,!z] [] hchild (by simpa using hr)
   simp [hempty] at ht
 have hv := subtree_vertex T B [s,!z] hchild
 have hcut : [s,!z] ∈ cuts T b c := by
   simp [cuts,pendantOriginal,List.mem_filter,hv,hmP,hnot]
 simp [bSideWithoutA,bSideEdges,List.mem_filter,hcut,hlabelsP,hlabelsQ,hbL,hcL,haB]

theorem root_split_bside_empty_cherry (T L R : Tree) (s : Bool) (a b c : Nat)
 (hT : T=orient s L R) (hn : (leaves T).Nodup) (hch : ActualCherry T a b)
 (hbL : b ∈ leaves L) (hcR : c ∈ leaves R) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
 (hempty : bSideWithoutA T a b c = []) : L=.node (.leaf a) (.leaf b) ∨ L=.node (.leaf b) (.leaf a) := by
 have hparts := orient_nodup_parts L R s (by simpa [←hT] using hn)
 have hbR : b ∉ leaves R := hparts.2.2 b hbL
 have hcL : c ∉ leaves L := by intro hc; exact hparts.2.2 c hc hcR
 have hLch : ActualCherry L a b := by
   rw [hT] at hch
   rcases (cherry_orient_iff L R s a b).mp hch with ⟨hL,hR⟩|⟨hL,hR⟩|hL|hR
   · have he : c=b := by simpa [hR,leaves] using hcR
     exact False.elim (hbc he.symm)
   · have he : c=a := by simpa [hR,leaves] using hcR
     exact False.elim (hac he.symm)
   · exact hL
   · exact False.elim (hbR (actual_cherry_labels R a b hR).2)
 cases L with
 | leaf x => exact False.elim (actual_cherry_leaf_false a b x hLch)
 | node A B =>
   rcases (actual_cherry_node_iff A B a b).mp hLch with ⟨hA,hB⟩|⟨hA,hB⟩|hA|hB
   · left; simp [hA,hB]
   · right; simp [hA,hB]
   · have haA := (actual_cherry_labels A a b hA).1
     have hbA := (actual_cherry_labels A a b hA).2
     have hnAB := List.nodup_append.mp hparts.1
     have haB : a ∉ leaves B := fun haB => hnAB.2.2 a haA a haB rfl
     have hbB : b ∉ leaves B := fun hbB => hnAB.2.2 b hbA b hbB rfl
     have hm := bside_off_child T A B R s false a b c (by simpa [orient] using hT) hbA hcR haB hbB (by simpa [orient] using hcL)
     simp [hempty] at hm
   · have haB := (actual_cherry_labels B a b hB).1
     have hbB := (actual_cherry_labels B a b hB).2
     have hnAB := List.nodup_append.mp hparts.1
     have haA : a ∉ leaves A := fun haA => hnAB.2.2 a haA a haB rfl
     have hbA : b ∉ leaves A := fun hbA => hnAB.2.2 b hbA b hbB rfl
     have hm := bside_off_child T B A R s true a b c (by simpa [orient] using hT) hbB hcR haA hbA (by simpa [orient] using hcL)
     simp [hempty] at hm

theorem empty_side_hole_tail (L R C : Tree) (s : Bool) (P : List Nat) (p : RMAF.Vertex) (b : Nat)
 (hL : rootedSpan P L = []) (hs : subtree (orient s L R) p = some C) (hbC : b ∈ leaves C)
 (hbR : b ∉ leaves R) : p.dropLast ∉ minimalVertices P (orient s L R) := by
 have hroot : ([] : RMAF.Vertex) ∉ minimalVertices P (orient s L R) := by
   cases hr : rootedSpan P R <;> cases s <;> simp [orient,minimalVertices,hL,hr,prependSide]
 cases p with
 | nil => simpa using hroot
 | cons z p =>
   cases s <;> cases z
   · cases p with
     | nil => simpa using hroot
     | cons u p =>
       intro hm
       have hr := minimal_subset_rooted P (.node L R) _ hm
       have ht := rooted_trace_subtree P (.node L R) L [false] ((u::p).dropLast) rfl (by simpa using hr)
       simp [hL] at ht
   · have hb := (subtree_leaves_sublist R p C hs).subset hbC
     exact False.elim (hbR hb)
   · have hb := (subtree_leaves_sublist R p C hs).subset hbC
     exact False.elim (hbR hb)
   · cases p with
     | nil => simpa using hroot
     | cons u p =>
       intro hm
       have hr := minimal_subset_rooted P (.node R L) _ hm
       have ht := rooted_trace_subtree P (.node R L) L [true] ((u::p).dropLast) rfl (by simpa using hr)
       simp [hL] at ht

theorem fallback_lca_nonroot {T S : Tree} (D : LiteralGeometry T S)
 (hbs : bSideWithoutA T D.a D.b D.c = []) : lca D.ub D.uc ≠ [] := by
 intro hroot
 rcases source_label_separation D with ⟨hab,hac,hbc,haX,hbX,hcX⟩
 obtain ⟨L,R,s,hs,hbL,hcR⟩ := lca_branch T D.ub D.uc D.b D.c D.leafB D.leafC hbc
 have hT : T=orient s L R := by simpa [hroot,subtree] using hs
 have hL := root_split_bside_empty_cherry T L R s D.a D.b D.c hT D.properT D.cherry hbL hcR hab hac hbc hbs
 have hparts := orient_nodup_parts L R s (by simpa [←hT] using D.properT)
 have hXL : rootedSpan (leaves D.X) L = [] := by
   rcases hL with hL|hL <;> rw [hL] <;> simp [rootedSpan,haX,hbX]
 have htail := empty_side_hole_tail L R D.C s (leaves D.X) D.r D.b hXL (by simpa [hT] using D.core) D.bC (hparts.2.2 D.b hbL)
 exact htail (by simpa [hT] using D.tailR)

#print axioms fallback_lca_nonroot
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping VertexGeometry BinaryExchange

theorem core_labels_inside_lca {T S : Tree} (D : LiteralGeometry T S) (U : Tree)
 (hU : subtree T (lca D.ub D.uc) = some U) (hbU : D.b ∈ leaves U) (hcU : D.c ∈ leaves U) :
 ∀ y ∈ leaves D.C, y ∈ leaves U := by
 have hqc := rooted_subtree_root [D.c] T U (lca D.ub D.uc) hU D.c hcU (by simp)
 have hsep := original_subtree_stem_separated T D.C D.r (leaves D.C) [D.c] D.properT D.core (fun _ hx => hx) (by
   intro x hx hxc
   have he : x=D.c := by simpa using hxc
   subst x
   exact D.cC hx)
 intro y hyC
 by_cases hyU : y ∈ leaves U
 · exact hyU
 have hyT := (subtree_leaves_sublist T D.r D.C D.core).subset hyC
 have hm := subtree_root_crossing (leaves D.C) T U (lca D.ub D.uc) hU D.b y hbU D.bC hyT hyC hyU
 have hd := List.all_eq_true.mp hsep _ hqc
 simp [disjointVertices,List.contains_iff_mem,hm] at hd

theorem proper_subtree_outside (T U : Tree) (q : RMAF.Vertex)
 (hn : (leaves T).Nodup) (hq : q ≠ []) (hs : subtree T q = some U) :
 ∃ y ∈ leaves T, y ∉ leaves U := by
 cases q with
 | nil => exact False.elim (hq rfl)
 | cons s p =>
   cases T with
   | leaf x => simp [subtree] at hs
   | node l r =>
     simp only [leaves,List.nodup_append] at hn
     cases s with
     | false =>
       obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil (leaves r) (leaves_nonempty r)
       refine ⟨y,List.mem_append_right _ hy,?_⟩
       intro hyU
       exact hn.2.2 y ((subtree_leaves_sublist l p U hs).subset hyU) y hy rfl
     | true =>
       obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil (leaves l) (leaves_nonempty l)
       refine ⟨y,List.mem_append_left _ hy,?_⟩
       intro hyU
       exact hn.2.2 y hy y ((subtree_leaves_sublist r p U hs).subset hyU) rfl

theorem literal_fallback_target_guard {T S : Tree} (D : LiteralGeometry T S)
 (hbs : bSideWithoutA T D.a D.b D.c = []) :
 currentGuard T S (targetBranch T [D.qa,lca D.ub D.uc]) = true := by
 let q := lca D.ub D.uc
 obtain ⟨U,hU,hbU,hcU,hqmin⟩ := literal_lca_subtree D
 have hqne : q ≠ [] := fallback_lca_nonroot D hbs
 have hlabels : subtreeLabels T q = leaves U := subtreeLabels_of_subtree T U q hU
 have hsep := source_label_separation D
 have haT : D.a ∈ leaves T := (subtree_leaves_sublist T D.qa (.leaf D.a) D.leafA).subset (by simp [leaves])
 have hbT : D.b ∈ leaves T := (subtree_leaves_sublist T D.r D.C D.core).subset D.bC
 have haC : D.a ∈ leaves D.C := (D.coreLabels D.a haT).mpr ⟨hsep.2.2.2.1,hsep.2.1⟩
 have haU := core_labels_inside_lca D U hU hbU hcU D.a haC
 have hqaLabel := subtreeLabels_of_leaf T D.qa D.a D.leafA
 have hqaneq : D.qa ≠ q := by
   intro he
   have hbqa : D.b ∈ subtreeLabels T D.qa := by simpa [he,hlabels] using hbU
   have heba : D.b=D.a := by simpa [hqaLabel] using hbqa
   exact hsep.1 heba.symm
 have hqaroot : D.qa ≠ [] := by
   intro he
   have heT : T=.leaf D.a := by simpa [he,LeafAt,subtree] using D.leafA
   have heba : D.b=D.a := by simpa [heT,leaves] using hbT
   exact hsep.1 heba.symm
 let R := (leaves T).filter (fun x => x != D.a)
 let F := singletonPartition T D.a
 let f := (subtreeLabels T q).contains
 have hbR : D.b ∈ R := by simp [R,hbT,Ne.symm hsep.1]
 have hRne : R ≠ [] := by intro he; have hh := hbR; simp [he] at hh
 have hstart := singleton_arc_partition T D.qa D.a D.properT D.leafA hRne
 have hinit : splitForest [leaves T] (subtreeLabels T D.qa) = F := by simpa [arcPartition,arcPartitionFrom] using hstart
 have harc : arcPartition T [D.qa,q] = splitAll F f := by
   change splitForest (splitForest [leaves T] (subtreeLabels T D.qa)) (subtreeLabels T q) = _
   rw [hinit]
   rfl
 have hnoncross : ¬ Cross [D.a] f := by
   intro hh
   have he : no [D.a] f = [] := by simp [no,f,hlabels,haU]
   exact hh.2 he
 have hcross : Cross R f := by
   obtain ⟨y,hyT,hyU⟩ := proper_subtree_outside T U q D.properT hqne hU
   have hya : y ≠ D.a := by intro he; subst y; exact hyU haU
   have hyR : y ∈ R := by simp [R,hyT,hya]
   constructor
   · intro he
     have hm : D.b ∈ yes R f := List.mem_filter.mpr ⟨hbR,by simp [f,hlabels,hbU]⟩
     simp [he] at hm
   · intro he
     have hm : y ∈ no R f := List.mem_filter.mpr ⟨hyR,by simp [f,hlabels,hyU]⟩
     simp [he] at hm
 have hcount : (arcPartition T [D.qa,q]).length = 3 := by
   rw [harc]
   change (splitAll [[D.a],R] f).length = 3
   simp only [splitAll,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
   rw [split_length_nocross [D.a] f (by simp) hnoncross,split_length_cross R f hcross]
 have hv : ∀ p ∈ [D.qa,q], p ∈ vertices T := by
   intro p hp
   simp at hp
   rcases hp with he|he
   · subst p; exact subtree_vertex T (.leaf D.a) D.qa D.leafA
   · subst p; exact subtree_vertex T U q hU
 have hAF := agreement_arc_from T [leaves T] [D.qa,q] D.properT (agreement_self_one T D.properT) hv
 have hh := hAF
 simp only [agreement,Bool.and_eq_true] at hh
 have hpart := hh.1.1.1.1
 have hemb := hh.1.2
 change partitionCheck (leaves T) (arcPartition T [D.qa,q]) = true at hpart
 change pairwiseEmbeddings T (arcPartition T [D.qa,q]) = true at hemb
 have hqSub : subtree T q = some U := hU
 have haSub : subtree T D.qa = some (.leaf D.a) := D.leafA
 simpa only [q] using (show currentGuard T S (targetBranch T [D.qa,q]) = true from by
   simp [currentGuard,current,targetBranch,paid,hqaroot,hqne,hqaneq,haSub,hqSub,hpart,hemb,hcount])

#print axioms literal_fallback_target_guard
end ExceptionalTarget

set_option autoImplicit false
namespace ExceptionalTarget
open RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching
open Universal233.Case322Extraction Universal233.Case322PaidGuard Universal233.Rule5Case322
open GenericG0Exchange G0Resume G0Shared OriginalEdgeClipping VertexGeometry BinaryExchange

theorem typeII_list_target_guard (T S : Tree) (a b : Nat) (qa qb : RMAF.Vertex) (qs : List RMAF.Vertex) (child : Branch)
 (hm : child ∈ typeIIBranches T S a b qa qb qs) (hr : child.role = .target)
 (hg : currentGuard T S (targetBranch T (qa::qs)) = true) : currentGuard T S child = true := by
 simp [typeIIBranches] at hm
 rcases hm with he|he|he
 · subst child; simp [hardBranch] at hr
 · subst child; simp [bBranch] at hr
 · subst child; exact hg

theorem literal_target_guard {T S : Tree} (D : LiteralGeometry T S) (child : Branch)
 (hm : child ∈ literalPlan D) (hr : child.role = .target) : currentGuard T S child = true := by
 have noI : (cSideEdges T D.b D.c).length < 2 → currentGuard T S child = true := by
   intro hsmall
   have hraw : literalPlan D = match bSideWithoutA T D.a D.b D.c with
    | [] => typeIIBranches T S D.a D.b D.qa (bArc D.w D.sb) [lca D.ub D.uc]
    | qs => typeIIBranches T S D.a D.b D.qa (bArc D.w D.sb) qs := by
     cases hcs : cSideEdges T D.b D.c with
     | nil => simp only [literalPlan,rawPlan,hcs] <;> rfl
     | cons q qs =>
       cases qs with
       | nil => simp only [literalPlan,rawPlan,hcs] <;> rfl
       | cons r rs => simp [hcs] at hsmall; omega
   rw [hraw] at hm
   cases hbs : bSideWithoutA T D.a D.b D.c with
   | nil =>
     have hmem : child ∈ typeIIBranches T S D.a D.b D.qa (bArc D.w D.sb) [lca D.ub D.uc] := by simpa [hbs] using hm
     exact typeII_list_target_guard T S D.a D.b D.qa (bArc D.w D.sb) [lca D.ub D.uc] child hmem hr (literal_fallback_target_guard D hbs)
   | cons q qs =>
     have hmem : child ∈ typeIIBranches T S D.a D.b D.qa (bArc D.w D.sb) (q::qs) := by simpa [hbs] using hm
     apply typeII_list_target_guard T S D.a D.b D.qa (bArc D.w D.sb) (q::qs) child hmem hr
     simpa [hbs] using literal_typeII_target_guard D
 cases hcs : cSideEdges T D.b D.c with
 | nil => exact noI (by simp [hcs])
 | cons q qs =>
   cases qs with
   | nil => exact noI (by simp [hcs])
   | cons r rs =>
     have hmem : child ∈ typeIBranches T S D.a D.b D.qa (bArc D.w D.sb) q r := by simpa [literalPlan,rawPlan,hcs] using hm
     simp [typeIBranches] at hmem
     rcases hmem with he|he|he|he
     · subst child; simp [hardBranch] at hr
     · subst child; simp [bBranch] at hr
     · subst child; exact cside_target_guard D q (by simp [hcs])
     · subst child; exact cside_target_guard D r (by simp [hcs])

theorem exceptional_actual_target {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (ha : [D.a] ∈ G) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B) :
 ∃ child ∈ guardedPlan D, child.role = .target ∧ Refines G child.partition := by
 obtain ⟨child,hraw,hrole,href⟩ := exceptional_raw_target D G B h ha hB hb hc
 exact ⟨child,List.mem_filter.mpr ⟨hraw,literal_target_guard D child hraw hrole⟩,hrole,href⟩

theorem exceptional_target_goal : ExceptionalTargetGoal := by
 intro T S D G B h ha hB hb hc hx
 obtain ⟨child,hguard,hrole,href⟩ := exceptional_actual_target D G B h ha hB hb hc
 exact ⟨child,hguard,href⟩

theorem exceptional_G0 {T S : Tree} (D : LiteralGeometry T S) (G : List (List Nat)) (B : List Nat)
 (h : agreement T S G = true) (ha : [D.a] ∈ G) (hB : B ∈ G) (hb : D.b ∈ B) (hc : D.c ∈ B)
 (hx : ∃ x ∈ B, x ∈ leaves D.X) :
 ∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧ H.length ≤ G.length ∧ Refines H child.partition := by
 obtain ⟨child,hguard,hrole,href⟩ := exceptional_actual_target D G B h ha hB hb hc
 exact ⟨child,hguard,G,h,Nat.le_refl _,href⟩

#print axioms literal_target_guard
#print axioms exceptional_actual_target
#print axioms exceptional_target_goal
#print axioms exceptional_G0
end ExceptionalTarget

set_option autoImplicit false
namespace RootGenericG0
open RMAF Universal233.CoreGraph Universal233.Case322PaidGuard VertexGeometry

theorem generic_g0_survival (T S : Tree) (D : LiteralGeometry T S)
    (G : List (List Nat)) (hg : agreement T S G = true) :
    ∃ child ∈ guardedPlan D, ∃ H, agreement T S H = true ∧
      H.length ≤ G.length ∧ Refines H child.partition := by
  rcases RootNonexceptionalG0.g0_witness_or_exceptional D G hg with
    h | ⟨ha,B,hB,hb,hc,hx⟩
  · exact h
  · exact ExceptionalTarget.exceptional_G0 D G B hg ha hB hb hc hx

#print generic_g0_survival
#print axioms generic_g0_survival
end RootGenericG0
