import AdmittedGeometry
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local

theorem clear_prepend (s : Bool) {A B : List RMAF.Vertex}
 (h : RestrictionBridge.Clear A B) :
 RestrictionBridge.Clear (prependSide s A) (prependSide s B) := by
 intro v hv hw
 obtain ⟨u,hu,rfl⟩ := List.mem_map.1 hv
 obtain ⟨w,hw,he⟩ := List.mem_map.1 hw
 have e : w = u := (List.cons.inj he).2
 exact h u hu (e ▸ hw)

theorem clear_opposite {A B : List RMAF.Vertex} :
 RestrictionBridge.Clear (prependSide false A) (prependSide true B) := by
 intro v hv hw
 obtain ⟨u,hu,rfl⟩ := List.mem_map.1 hv
 obtain ⟨w,hw,he⟩ := List.mem_map.1 hw
 simp at he

theorem no_selected_subtree_hull {T : Tree} {D : List Nat} {a u : RMAF.Vertex}
 (no : ∀ x, x ∈ D → x ∉ subtreeLabels T a) (ap : a <+: u) :
 u ∉ minimalVertices D T := by
 intro hu
 obtain ⟨v,hv,hpath⟩ := hull_subset_reach _ u ((minimalVertices_correct D T u).1 hu)
 obtain ⟨x,hx,hvx⟩ := (selected_decompose_label D T v).1 hv
 exact no x hx ((subtreeLabels_prefix T a x).2
   ⟨v,(leafAt_selected T v x).2 hvx,ap.trans (path_root_prefix hpath)⟩)

/-- Different cherries of one proper rooted restriction have disjoint
original vertex embeddings. This is proved before using the Rule5 guards. -/
theorem distinct_cherries_clear {T : Tree} {p q r s : Nat}
 (hn : (leaves T).Nodup) (hc : HasCherry p q T) (hd : HasCherry r s T)
 (sep : p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s) :
 RestrictionBridge.Clear (minimalVertices [p,q] T) (minimalVertices [r,s] T) := by
 induction hc generalizing r s with
 | here =>
   have hr := (hasCherry_labels hd).1
   have hh : r = p ∨ r = q := by simpa [leaves] using hr
   exact False.elim (hh.elim (fun e => sep.1 e.symm) (fun e => sep.2.2.1 e.symm))
 | swap =>
   have hr := (hasCherry_labels hd).1
   have hh : r = q ∨ r = p := by simpa [leaves] using hr
   exact False.elim (hh.elim (fun e => sep.2.2.1 e.symm) (fun e => sep.1 e.symm))
 | @left l z hc ih =>
   obtain ⟨hnl,hnz,dj⟩ := List.nodup_append.1 hn
   have labs := hasCherry_labels hc
   have np : p ∉ leaves z := fun h => dj p labs.1 p h rfl
   have nq : q ∉ leaves z := fun h => dj q labs.2 q h rfl
   have hm := pairSpan_left labs.1 labs.2 np nq
   cases hd with
   | here => cases hc
   | swap => cases hc
   | left hd =>
     have ls := hasCherry_labels hd
     have nr : r ∉ leaves z := fun h => dj r ls.1 r h rfl
     have ns : s ∉ leaves z := fun h => dj s ls.2 s h rfl
     rw [hm,pairSpan_left ls.1 ls.2 nr ns]
     exact clear_prepend false (ih hnl hd sep)
   | right hd =>
     have ls := hasCherry_labels hd
     have nr : r ∉ leaves l := fun h => dj r h r ls.1 rfl
     have ns : s ∉ leaves l := fun h => dj s h s ls.2 rfl
     rw [hm,pairSpan_right ls.1 ls.2 nr ns]
     exact clear_opposite
 | @right z l hc ih =>
   obtain ⟨hnz,hnl,dj⟩ := List.nodup_append.1 hn
   have labs := hasCherry_labels hc
   have np : p ∉ leaves z := fun h => dj p h p labs.1 rfl
   have nq : q ∉ leaves z := fun h => dj q h q labs.2 rfl
   have hm := pairSpan_right labs.1 labs.2 np nq
   cases hd with
   | here => cases hc
   | swap => cases hc
   | left hd =>
     have ls := hasCherry_labels hd
     have nr : r ∉ leaves l := fun h => dj r ls.1 r h rfl
     have ns : s ∉ leaves l := fun h => dj s ls.2 s h rfl
     rw [hm,pairSpan_left ls.1 ls.2 nr ns]
     exact (RestrictionBridge.clear_symm _ _).1 clear_opposite
   | right hd =>
     have ls := hasCherry_labels hd
     have nr : r ∉ leaves z := fun h => dj r h r ls.1 rfl
     have ns : s ∉ leaves z := fun h => dj s h s ls.2 rfl
     rw [hm,pairSpan_right ls.1 ls.2 nr ns]
     exact clear_prepend true (ih hnl hd sep)

/-- Two actual good-block cherries cannot both survive the reverse priority
guard. Their two target pendant regions would have the same nonempty Y,
forcing the two disjoint cherry paths to use one original parent vertex. -/
theorem guarded_no_separated_good_cherries {T S : Tree} {X Y Z : List Nat}
 {i j : RMAF.Vertex} {p q r s : Nat}
 (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y,Z] = true)
 (he : pairwiseEmbeddings T [X,Y,Z] = true)
 (early : earlierClear S T = true) (good : restrictionAgrees T S X = true)
 (cp : CherryAt S i p q) (cr : CherryAt S j r s)
 (pX : p ∈ X) (qX : q ∈ X) (rX : r ∈ X) (sX : s ∈ X)
 (sep : p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s) : False := by
 obtain ⟨U,hU,hpU⟩ := restrict_hasCherry (actual_hasCherry cp) X pX qX
 cases hV : restrict X T with
 | none => simp [restrictionAgrees,hU,hV] at good
 | some V =>
   have iso : RootedIso V U := (sameShape_correct V U).1 (by simpa [restrictionAgrees,hU,hV] using good)
   have hpV := iso_hasCherry (BinaryExchange.iso_symm iso) hpU
   obtain ⟨W,hW,hrW⟩ := restrict_hasCherry (actual_hasCherry cr) X rX sX
   have e : W = U := Option.some.inj (hW.symm.trans hU)
   subst W
   have hrV := iso_hasCherry (BinaryExchange.iso_symm iso) hrW
   have ndV : (leaves V).Nodup := by rw [restrict_leaves hV]; exact hn.filter _
   have smallclear := distinct_cherries_clear ndV hpV hrV sep
   have bigclear := ((RestrictionBridge.literal_clear_transport T V X [p,q] [r,s] hV
     (by intro x hx; have hh : x = p ∨ x = q := by simpa using hx
         rcases hh with rfl | rfl <;> assumption)
     (by intro x hx; have hh : x = r ∨ x = s := by simpa using hx
         rcases hh with rfl | rfl <;> assumption)).2).2 smallclear
   obtain ⟨u,v,hu,hpatt,_⟩ := guarded_good_cherry_attachment hn hp he early good cp pX qX
   obtain ⟨w,z,hw,hratt,_⟩ := guarded_good_cherry_attachment hn hp he early good cr rX sX
   have chooseY {a b : RMAF.Vertex}
    (ha : (((∀ x, x ∈ subtreeLabels T a ↔ x ∈ Y) ∧ (∀ x, x ∈ subtreeLabels T b ↔ x ∈ Z)) ∨
      ((∀ x, x ∈ subtreeLabels T a ↔ x ∈ Z) ∧ (∀ x, x ∈ subtreeLabels T b ↔ x ∈ Y)))) :
    ∃ e, e ∈ [a,b] ∧ ∀ x, x ∈ subtreeLabels T e ↔ x ∈ Y := by
     rcases ha with ⟨h,_⟩ | ⟨_,h⟩
     · exact ⟨a,by simp,h⟩
     · exact ⟨b,by simp,h⟩
   obtain ⟨a,ha,ay⟩ := chooseY hpatt
   obtain ⟨b,hb,byy⟩ := chooseY hratt
   have acut : a ∈ cuts T p q := by simpa [hu] using ha
   have bcut : b ∈ cuts T r s := by simpa [hw] using hb
   have noY : ∀ x, x ∈ X → x ∉ Y := by
     intro x hx hy
     obtain ⟨l,hl⟩ := leaf_exists (block_labels hp (by simp) hx)
     have part := (executable_pairwiseEmbeddings T [X,Y,Z]).1 he
     have dj : BinaryExchange.Disj T X Y := (List.pairwise_cons.1 part).1 Y (by simp)
     exact dj l ⟨(minimalVertices_correct X T l).1 ((minimalVertices_terminal X T l x hl).2 hx),
       (minimalVertices_correct Y T l).1 ((minimalVertices_terminal Y T l x hl).2 hy)⟩
   have ae : a = b := by
     obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil Y (RestrictionBridge.checked_nonempty _ _ hp Y (by simp))
     obtain ⟨u,hu,hau⟩ := (subtreeLabels_prefix T a y).1 ((ay y).2 hy)
     obtain ⟨v,hv,hbv⟩ := (subtreeLabels_prefix T b y).1 ((byy y).2 hy)
     have euv := leaf_unique hn hu hv
     rw [euv] at hau
     rcases List.prefix_or_prefix_of_prefix hau hbv with hab | hba
     · apply Classical.byContradiction
       intro nab
       obtain ⟨tail,heq⟩ := hab
       have ane : tail ≠ [] := by intro hnil; simp [hnil] at heq; exact nab heq
       have bparent : a <+: b.dropLast := by
         rw [←heq,List.dropLast_append_of_ne_nil ane]
         exact List.prefix_append _ _
       have bp : b.dropLast ∈ minimalVertices [r,s] T := ((cuts_spec T r s b).1 bcut).2.2.1
       have rn : r ∉ subtreeLabels T a := fun h => noY r rX ((ay r).1 h)
       have sn : s ∉ subtreeLabels T a := fun h => noY s sX ((ay s).1 h)
       have noHull := no_selected_subtree_hull (D:=[r,s])
         (by intro x hx; have hh : x = r ∨ x = s := by simpa using hx
             rcases hh with rfl | rfl <;> assumption) bparent
       exact noHull bp
     · apply Classical.byContradiction
       intro nab
       obtain ⟨tail,heq⟩ := hba
       have ane : tail ≠ [] := by intro hnil; simp [hnil] at heq; exact nab heq.symm
       have aparent : b <+: a.dropLast := by
         rw [←heq,List.dropLast_append_of_ne_nil ane]
         exact List.prefix_append _ _
       have ap : a.dropLast ∈ minimalVertices [p,q] T := ((cuts_spec T p q a).1 acut).2.2.1
       have pn : p ∉ subtreeLabels T b := fun h => noY p pX ((byy p).1 h)
       have qn : q ∉ subtreeLabels T b := fun h => noY q qX ((byy q).1 h)
       exact (no_selected_subtree_hull (D:=[p,q])
         (by intro x hx; have hh : x = p ∨ x = q := by simpa using hx
             rcases hh with rfl | rfl <;> assumption) aparent) ap
   exact bigclear a.dropLast ((cuts_spec T p q a).1 acut).2.2.1
     (ae.symm ▸ ((cuts_spec T r s b).1 bcut).2.2.1)

inductive Caterpillar : Tree → Prop where
 | leaf (x) : Caterpillar (.leaf x)
 | left (x) {T} : Caterpillar T → Caterpillar (.node (.leaf x) T)
 | right (x) {T} : Caterpillar T → Caterpillar (.node T (.leaf x))

def NoSeparatedCherries (T : Tree) : Prop :=
 ∀ i j p q r s, CherryAt T i p q → CherryAt T j r s →
   p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s → False

theorem tree_leaf_or_cherry (T : Tree) :
 (∃ x, T = .leaf x) ∨ ∃ i a b, CherryAt T i a b := by
 induction T with
 | leaf x => exact Or.inl ⟨x,rfl⟩
 | node l r ihl ihr =>
   right
   rcases ihl with ⟨x,rfl⟩ | ⟨i,a,b,h⟩
   · rcases ihr with ⟨y,rfl⟩ | ⟨i,a,b,h⟩
     · exact ⟨[],x,y,rfl⟩
     · exact ⟨true::i,a,b,h⟩
   · exact ⟨false::i,a,b,h⟩

theorem node_contains_cherry (l r : Tree) :
 ∃ i a b, CherryAt (.node l r) i a b := by
 rcases tree_leaf_or_cherry (.node l r) with ⟨x,h⟩ | h
 · cases h
 · exact h

theorem caterpillar_of_no_separated {T : Tree} (hn : (leaves T).Nodup)
 (no : NoSeparatedCherries T) : Caterpillar T := by
 induction T with
 | leaf x => exact .leaf x
 | node l r ihl ihr =>
   obtain ⟨hnl,hnr,dj⟩ := List.nodup_append.1 hn
   have nol : NoSeparatedCherries l := by
     intro i j p q a b hp ha sep
     exact no (false::i) (false::j) p q a b hp ha sep
   have nor : NoSeparatedCherries r := by
     intro i j p q a b hp ha sep
     exact no (true::i) (true::j) p q a b hp ha sep
   cases l with
   | leaf x => exact .left x (ihr hnr nor)
   | node ll lr =>
     cases r with
     | leaf y => exact .right y (ihl hnl nol)
     | node rl rr =>
       obtain ⟨i,p,q,hpq⟩ := node_contains_cherry ll lr
       obtain ⟨j,a,b,hab⟩ := node_contains_cherry rl rr
       have pl := (hasCherry_labels (actual_hasCherry hpq)).1
       have ql := (hasCherry_labels (actual_hasCherry hpq)).2
       have ar := (hasCherry_labels (actual_hasCherry hab)).1
       have br := (hasCherry_labels (actual_hasCherry hab)).2
       have sep : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b :=
         ⟨dj p pl a ar,dj p pl b br,dj q ql a ar,dj q ql b br⟩
       exact False.elim (no (false::i) (true::j) p q a b hpq hab sep)

theorem caterpillar_cherry_count {T : Tree} (hc : Caterpillar T) :
 (cherries T).length ≤ 1 := by
 induction hc with
 | leaf x => simp [cherries]
 | @left x T hc ih =>
   cases T with
   | leaf y => simp [cherries]
   | node l r => simpa [cherries] using ih
 | @right x T hc ih =>
   cases T with
   | leaf y => simp [cherries]
   | node l r => simpa [cherries] using ih

theorem caterpillar_nonleaf_unique {l r : Tree} (hc : Caterpillar (.node l r)) :
 (cherries (.node l r)).length = 1 := by
 obtain ⟨i,a,b,h⟩ := node_contains_cherry l r
 have hm := cherries_complete (.node l r) i a b h
 have pos := List.length_pos_of_mem hm
 have upper := caterpillar_cherry_count hc
 omega

/-- The caterpillar conclusion is obtained from original priority guards and
an actual good source subtree. No caterpillar, unique-cherry, or attachment
witness is an input. The source subtree may be at any original address. -/
theorem guarded_good_subtree_caterpillar {T S U : Tree} {X Y Z : List Nat}
 {e : RMAF.Vertex}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (hU : subtree S e = some U) (hx : leaves U = X)
 (hp : partitionCheck (leaves T) [X,Y,Z] = true)
 (he : pairwiseEmbeddings T [X,Y,Z] = true)
 (early : earlierClear S T = true) (good : restrictionAgrees T S X = true) :
 Caterpillar U ∧ (cherries U).length ≤ 1 := by
 have hnU : (leaves U).Nodup := by
   rw [←source_subtree_labels hU]
   exact (subtreeLabels_sublist S e).nodup hnS
 have no : NoSeparatedCherries U := by
   intro i j p q r s cp cr sep
   have cps : CherryAt S (e ++ i) p q := by unfold CherryAt; rw [subtree_append hU]; exact cp
   have crs : CherryAt S (e ++ j) r s := by unfold CherryAt; rw [subtree_append hU]; exact cr
   have lp := hasCherry_labels (actual_hasCherry cp)
   have lr := hasCherry_labels (actual_hasCherry cr)
   exact guarded_no_separated_good_cherries hnT hp he early good cps crs
     (hx ▸ lp.1) (hx ▸ lp.2) (hx ▸ lr.1) (hx ▸ lr.2) sep
 have cat := caterpillar_of_no_separated hnU no
 exact ⟨cat,caterpillar_cherry_count cat⟩

theorem partition_swap_first (L X Y Z : List Nat) :
 partitionCheck L [X,Y,Z] = partitionCheck L [Y,X,Z] := by
 simp only [partitionCheck,List.all_cons,List.all_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
   List.count_append,List.all_append]
 simp only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Bool.and_comm,Bool.and_left_comm,Bool.and_assoc]

theorem embeddings_swap_first (T : Tree) (X Y Z : List Nat)
 (he : pairwiseEmbeddings T [X,Y,Z] = true) : pairwiseEmbeddings T [Y,X,Z] = true := by
 have hp := (executable_pairwiseEmbeddings T [X,Y,Z]).1 he
 have dxy := (List.pairwise_cons.1 hp).1 Y (by simp)
 have dxz := (List.pairwise_cons.1 hp).1 Z (by simp)
 have dyz := (List.pairwise_cons.1 (List.pairwise_cons.1 hp).2).1 Z (by simp)
 apply (executable_pairwiseEmbeddings T [Y,X,Z]).2
 apply List.pairwise_cons.2
 constructor
 · intro B hB
   have hh : B = X ∨ B = Z := by simpa using hB
   rcases hh with rfl | rfl
   · exact fun v h => dxy v ⟨h.2,h.1⟩
   · exact dyz
 · apply List.pairwise_cons.2
   constructor
   · intro B hB
     have e : B = Z := by simpa using hB
     subst B
     exact dxz
   · simp

theorem list_two_named {A : Type} (L : List A) (h : L.length = 2) :
 ∃ u v, L = [u,v] := by
 cases L with
 | nil => simp at h
 | cons u us =>
   cases us with
   | nil => simp at h
   | cons v vs =>
     have hv : vs = [] := by simpa using h
     exact ⟨u,v,by rw [hv]⟩

/-- Original admitted Rule5 guards imply the source's every good pendant is
a caterpillar. This specializes the graph argument to the executable source
cut list, in either pendant position and either original tree orientation. -/
theorem admitted_good_pendant_caterpillar {T S : Tree} {a b : Nat} {e : RMAF.Vertex}
 (ha : admitted T S a b = true) (he : e ∈ cuts S a b)
 (good : restrictionAgrees T S (subtreeLabels S e) = true) :
 ∃ U, subtree S e = some U ∧ Caterpillar U ∧ (cherries U).length ≤ 1 := by
 have parts := admitted_parts ha
 have proper := properPair_parts parts.1
 obtain ⟨u,v,hc⟩ := list_two_named (cuts S a b) parts.2.2.2.2
 obtain ⟨U,hU⟩ := ((cuts_spec S a b e).1 he).1
 have aT : a ∈ leaves T := by
   have hh : hasCherry T a b = true := by
     simp only [admitted,Bool.and_eq_true] at ha; exact ha.1.1.1.1.1.1.1.1.2
   unfold hasCherry at hh
   obtain ⟨⟨p,x,y⟩,hm,hxy⟩ := List.any_eq_true.1 hh
   have labs := hasCherry_labels (actual_hasCherry (cherries_sound T p x y hm))
   have xy : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by simpa using hxy
   rcases xy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
   · exact labs.1
   · exact labs.2
 have hsrc := pendant_partition_check (b:=b) proper.2.1 ((proper.2.2 a).1 aT)
 have hpT : partitionCheck (leaves T) (pendantPartition S a b) = true :=
   (RestrictionBridge.partition_labels_congr (leaves S) (leaves T) _ (fun x => (proper.2.2 x).symm)).1 hsrc
 have ex : leaves U = subtreeLabels S e := (source_subtree_labels hU).symm
 have em : e = u ∨ e = v := by simpa [hc] using he
 have pp : pendantPartition S a b = [subtreeLabels S u,subtreeLabels S v,coreLabels S a b] := by
   simp only [pendantPartition,hc,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
 rcases em with heu | hev
 · subst e
   have cat := guarded_good_subtree_caterpillar proper.1 proper.2.1 hU ex
     (pp ▸ hpT) (pp ▸ parts.2.2.2.1) parts.2.2.1 good
   exact ⟨U,hU,cat⟩
 · subst e
   have hp0 := pp ▸ hpT
   have hp1 : partitionCheck (leaves T) [subtreeLabels S v,subtreeLabels S u,coreLabels S a b] = true := by
     rw [←partition_swap_first]; exact hp0
   have he1 := embeddings_swap_first T _ _ _ (pp ▸ parts.2.2.2.1)
   have cat := guarded_good_subtree_caterpillar proper.1 proper.2.1 hU ex hp1 he1 parts.2.2.1 good
   exact ⟨U,hU,cat⟩

end Universal233.Rule5Classification
