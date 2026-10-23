import LargePendant
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local

theorem partition_perm {L : List Nat} {F G : List (List Nat)}
 (hp : partitionCheck L F = true) (perm : F.Perm G) : partitionCheck L G = true := by
 have p := BinaryExchange.partition_parts L F hp
 apply BinaryExchange.partition_intro
 · intro C hC; exact p.1 C (perm.mem_iff.2 hC)
 · intro x hx; rw [←perm.flatten.count_eq x]; exact p.2.1 x hx
 · intro x hx; exact p.2.2 x (perm.flatten.mem_iff.2 hx)

theorem agreement_perm {T S : Tree} {F G : List (List Nat)}
 (ha : agreement T S F = true) (perm : F.Perm G) : agreement T S G = true := by
 have p := BinaryExchange.agreement_parts T S F ha
 have epT : G.Pairwise (BinaryExchange.Disj T) := (perm.pairwise_iff
   (by intro X Y h v hv; exact h v ⟨hv.2,hv.1⟩)).1 p.2.2.2.1
 have epS : G.Pairwise (BinaryExchange.Disj S) := (perm.pairwise_iff
   (by intro X Y h v hv; exact h v ⟨hv.2,hv.1⟩)).1 p.2.2.2.2
 simp only [agreement,Bool.and_eq_true,List.all_eq_true,executable_pairwiseEmbeddings]
 exact ⟨⟨⟨⟨partition_perm p.1 perm,partition_perm p.2.1 perm⟩,
   fun C hC => p.2.2.1 C (perm.mem_iff.2 hC)⟩,epT⟩,epS⟩

def mergeGood (X : List Nat) (H : List (List Nat)) : List (List Nat) :=
 X :: H.filter (fun B => !RestrictionBridge.contained B X)

/-- Computed whole-good-component regrouping. Its AF validity, refinement,
and exact component-count saving follow from actual checked P and H; they
are not fields in a proposed exchange certificate. -/
theorem mergeGood_properties {T S U : Tree} {e : RMAF.Vertex} {P H : List (List Nat)} {X : List Nat}
 (hnS : (leaves S).Nodup) (hU : subtree S e = some U) (hxU : leaves U = X)
 (hp : partitionCheck (leaves S) P = true) (heT : pairwiseEmbeddings T P = true)
 (heS : pairwiseEmbeddings S P = true) (xm : X ∈ P)
 (good : restrictionAgrees T S X = true) (ha : agreement T S H = true) (href : Refines H P) :
 agreement T S (mergeGood X H) = true ∧ Refines (mergeGood X H) P ∧
 (mergeGood X H).length + (RestrictionBridge.family X H).length = H.length + 1 := by
 let A := RestrictionBridge.family X H
 let W := H.filter (fun B => !RestrictionBridge.contained B X)
 have ru : restrict X S = some U := hxU ▸ restrict_original_subtree hnS hU
 have hAX : partitionCheck X A = true := hxU ▸
   RestrictionBridge.local_partition S U X H P ru (source_agreement_checks ha).1 hp href xm
 have ndX : X.Nodup := hxU ▸ (by
   rw [←source_subtree_labels hU]
   exact (subtreeLabels_sublist S e).nodup hnS)
 have neX : X ≠ [] := hxU ▸ CutRealization.leaves_nonempty U
 have perm : (A ++ [] ++ W).Perm H := by
   simpa [A,W,RestrictionBridge.family] using
     (List.filter_append_perm (fun B => RestrictionBridge.contained B X) H)
 have orig := agreement_perm ha perm.symm
 have cross (T : Tree) (hP : pairwiseEmbeddings T P = true) : ∀ C, C ∈ W → BinaryExchange.Disj T X C := by
   intro C hC
   have cw := List.mem_filter.1 hC
   obtain ⟨Y,ym,sub⟩ := href C cw.1
   have nxy : X ≠ Y := by
     intro xy
     have yes := (RestrictionBridge.contained_iff C X).2 (xy.symm ▸ sub)
     simp [yes] at cw
   have dj := RestrictionBridge.pairwise_distinct T P hP X Y xm ym nxy
   have graph : BinaryExchange.Disj T X Y := by
     intro v hv
     exact dj v ((minimalVertices_correct X T v).2 hv.1) ((minimalVertices_correct Y T v).2 hv.2)
   exact BinaryExchange.disj_mono graph (fun _ hx => hx) sub
 have empty (T : Tree) : BinaryExchange.Disj T X [] := by
   intro v hv
   exact BinaryExchange.hull_none (BinaryExchange.selected_none [] T (by simp)) v hv.2
 have atU : BinaryExchange.treeAt S e = some U := by rw [source_treeAt]; exact hU
 have val := BinaryExchange.exchange_valid T S U e X [] A [] W hnS atU ndX neX hAX
   (by simp) orig good (empty T) (cross T heT)
   (by simpa [BinaryExchange.yes] using empty S)
   (by simpa [BinaryExchange.no] using empty S) (cross S heS)
 have valid : agreement T S (mergeGood X H) = true := by
   simpa [BinaryExchange.output,BinaryExchange.splitAll,mergeGood,W] using val
 have ref : Refines (mergeGood X H) P := by
   intro B hB
   rcases List.mem_cons.1 hB with bx | hB
   · subst B
     exact ⟨X,xm,fun _ hx => hx⟩
   · exact href B (List.mem_filter.1 hB).1
 have counts := perm.length_eq
 simp only [List.length_append,List.length_nil,Nat.add_zero] at counts
 exact ⟨valid,ref,by simp only [mergeGood,List.length_cons]; change W.length + 1 + A.length = H.length+1; omega⟩

theorem splitTwo_refines_original (F : List (List Nat)) (T : Tree) (u v : RMAF.Vertex) :
 Refines (splitTwo F T u v) F := by
 intro B hB
 obtain ⟨C,hC,hBC⟩ := List.mem_flatMap.1 hB
 obtain ⟨D,hD,hCD⟩ := List.mem_flatMap.1 hC
 exact ⟨D,hD,fun x hx => BinaryExchange.split_sub D C _ hCD x (BinaryExchange.split_sub C B _ hBC x hx)⟩

theorem flatten_singleton_lengths (A : List (List Nat))
 (one : ∀ B, B ∈ A → B.length = 1) : A.flatten.length = A.length := by
 induction A with
 | nil => rfl
 | cons B A ih =>
   have b := one B (by simp)
   have rest := ih (fun C hC => one C (by simp [hC]))
   simp [List.flatten_cons,List.length_append,b,rest,Nat.add_comm]

theorem refined_singleton_family_length {S U : Tree} {e : RMAF.Vertex} {P H F : List (List Nat)} {X : List Nat}
 (hnS : (leaves S).Nodup) (hU : subtree S e = some U) (hxU : leaves U = X)
 (hp : partitionCheck (leaves S) P = true) (xm : X ∈ P)
 (hH : partitionCheck (leaves S) H = true) (href : Refines H P) (hHF : Refines H F)
 (one : ∀ C, C ∈ F → ∀ x y, x ∈ C → y ∈ C → x ∈ X → y ∈ X → x = y) :
 (RestrictionBridge.family X H).length = X.length := by
 have ru : restrict X S = some U := hxU ▸ restrict_original_subtree hnS hU
 have hpX : partitionCheck X (RestrictionBridge.family X H) = true := hxU ▸
   RestrictionBridge.local_partition S U X H P ru hH hp href xm
 have ndX : X.Nodup := hxU ▸ (by
   rw [←source_subtree_labels hU]
   exact (subtreeLabels_sublist S e).nodup hnS)
 have ones : ∀ D, D ∈ RestrictionBridge.family X H → D.length = 1 := by
   intro D hD
   have dh := (RestrictionBridge.mem_family D X H).1 hD
   obtain ⟨C,hC,sub⟩ := hHF D dh.1
   obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil D (RestrictionBridge.checked_nonempty _ _ hH D dh.1)
   have eq := block_singleton_of_only hH dh.1 hy (by
     intro z hz
     exact one C hC z y (sub z hz) (sub y hy) (dh.2 hz) (dh.2 hy))
   simp [eq]
 have perm := RestrictionBridge.checked_flatten_perm X (RestrictionBridge.family X H) ndX hpX
 have len := perm.length_eq
 rw [flatten_singleton_lengths _ ones] at len
 exact len

theorem mixed_X_all_blocks_at_most_one {T S U V : Tree} {X : List Nat}
 {e : RMAF.Vertex} {p q : Nat} {F : List (List Nat)} {B : List Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (hU : subtree S e = some U) (hxU : leaves U = X)
 (hV : restrict X T = some V) (cat : Caterpillar V) (ch : HasCherry p q V)
 (good : restrictionAgrees T S X = true)
 (outside : ∀ z, z ∈ leaves T → z ∉ X → ∃ r, r ∈ cuts T p q ∧ z ∈ subtreeLabels T r)
 (ha : agreement T S F = true) (hB : B ∈ F)
 {x z : Nat} (xB : x ∈ B) (zB : z ∈ B) (xX : x ∈ X) (zX : z ∉ X) :
 ∀ C, C ∈ F → ∀ u v, u ∈ C → v ∈ C → u ∈ X → v ∈ X → u = v := by
 intro C hC u v uC vC uX vX
 apply Classical.byContradiction
 intro uv
 by_cases cb : C = B
 · subst C
   exact good_pendant_mixed_at_most_one hnT hnS hU hxU hV cat ch outside ha hB uC vC zB uX vX zX uv
 · exact mixed_block_forbids_other_X_pair hnT hnS hU hxU hV cat ch good outside ha hB hC
     (Ne.symm cb) xB zB xX zX uC vC uX vX uv

theorem mixed_split_merge_saves {T S U V : Tree} {X : List Nat}
 {e u v : RMAF.Vertex} {p q : Nat} {P F : List (List Nat)} {B : List Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (hU : subtree S e = some U) (hxU : leaves U = X)
 (hV : restrict X T = some V) (cat : Caterpillar V) (ch : HasCherry p q V)
 (good : restrictionAgrees T S X = true)
 (outside : ∀ z, z ∈ leaves T → z ∉ X → ∃ r, r ∈ cuts T p q ∧ z ∈ subtreeLabels T r)
 (hp : partitionCheck (leaves S) P = true) (heT : pairwiseEmbeddings T P = true)
 (heS : pairwiseEmbeddings S P = true) (xm : X ∈ P) (size : 3 ≤ X.length)
 (ha : agreement T S F = true) (cutEq : cuts T p q = [u,v])
 (href : Refines (splitTwo F T u v) P) (hB : B ∈ F)
 {x z : Nat} (xB : x ∈ B) (zB : z ∈ B) (xX : x ∈ X) (zX : z ∉ X) :
 agreement T S (mergeGood X (splitTwo F T u v)) = true ∧
 (mergeGood X (splitTwo F T u v)).length ≤ F.length ∧
 Refines (mergeGood X (splitTwo F T u v)) P := by
 have hspl := splitTwo_original hnT cutEq (agreement_symm ha)
 have hH := agreement_symm hspl.1
 have allone := mixed_X_all_blocks_at_most_one hnT hnS hU hxU hV cat ch good outside ha hB xB zB xX zX
 have flen := refined_singleton_family_length hnS hU hxU hp xm (source_agreement_checks hH).1 href
   (splitTwo_refines_original F T u v) allone
 have merged := mergeGood_properties hnS hU hxU hp heT heS xm good hH href
 rw [flen] at merged
 exact ⟨merged.1,by omega,merged.2.1⟩

theorem no_mixed_core_split_saving {T S : Tree} {F : List (List Nat)}
 {p q : Nat} {u v : RMAF.Vertex}
 (hnT : (leaves T).Nodup) (ha : agreement S T F = true) (cutEq : cuts T p q = [u,v])
 (nomix : ∀ C, C ∈ F → ∀ x y, x ∈ C → y ∈ C →
   x ∈ coreLabels T p q → y ∈ coreLabels T p q) :
 (splitTwo F T u v).length ≤ F.length + 1 := by
 have um : u ∈ cuts T p q := by simp [cutEq]
 have vm : v ∈ cuts T p q := by simp [cutEq]
 have unev : u ≠ v := by
   have nd := pendantOriginal_nodup T p q
   change (cuts T p q).Nodup at nd
   simpa [cutEq] using nd
 have dj := pendant_labelsets_disjoint hnT um vm unev
 obtain ⟨U,hU⟩ := ((cuts_spec T p q u).1 um).1
 have first := split_original_agreement hnT hU ha
 rw [←source_subtree_labels hU] at first
 let H := splitForest F (subtreeLabels T u)
 have zero : H.filter (fun D => BinaryExchange.mixed D (subtreeLabels T v).contains) = [] := by
   apply List.filter_eq_nil_iff.2
   intro D hD
   cases hm : BinaryExchange.mixed D (subtreeLabels T v).contains with
   | false => simp
   | true =>
     obtain ⟨⟨a,aD,av⟩,⟨b,bD,bv⟩⟩ := (BinaryExchange.mixed_iff D _).1 hm
     have av : a ∈ subtreeLabels T v := List.contains_iff_mem.1 av
     have bv : b ∉ subtreeLabels T v := by simpa using bv
     obtain ⟨C,hC,dc⟩ := List.mem_flatMap.1 hD
     have sub := BinaryExchange.split_sub C D (subtreeLabels T u).contains dc
     rcases BinaryExchange.split_mono C (subtreeLabels T u).contains D dc with yesU | noU
     · exact False.elim (dj a (List.contains_iff_mem.1 (yesU a aD)) av)
     · have bu : b ∉ subtreeLabels T u := by simpa using noU b bD
       have bT := block_labels (source_agreement_checks ha).1 hC (sub b bD)
       have bc : b ∈ coreLabels T p q := (mem_core T p q b).2 ⟨bT,by
         intro r hr
         have rr : r = u ∨ r = v := by simpa [cutEq] using hr
         rcases rr with rfl | rfl <;> assumption⟩
       have ac := nomix C hC b a (sub b bD) (sub a aD) bc
       exact False.elim (((mem_core T p q a).1 ac).2 v vm av)
 have second := BinaryExchange.splitAll_length H (subtreeLabels T v).contains
 rw [zero] at second
 change (splitTwo F T u v).length ≤ H.length + 0 at second
 change (agreement S T H = true ∧ H.length ≤ F.length+1) at first
 omega

/-- Complete large-good-pendant graph exchange after the classification
lemmas have produced its actual cherry, restrictions and two target arcs.
The saving is derived separately for actual mixed-X and no-mixed-X forests. -/
theorem large_good_cherry_exchange {T S U V : Tree} {X : List Nat}
 {e i u v : RMAF.Vertex} {p q : Nat} {P F : List (List Nat)}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hU : subtree S e = some U) (hxU : leaves U = X)
 (hV : restrict X T = some V) (cat : Caterpillar V) (ch : HasCherry p q V)
 (cpq : CherryAt S i p q) (cutEq : cuts T p q = [u,v])
 (core : ∀ x, x ∈ coreLabels T p q ↔ x ∈ X)
 (mapP : ∀ C, C ∈ pendantPartition T p q → ∃ D, D ∈ P ∧ C ⊆ D)
 (good : restrictionAgrees T S X = true)
 (hp : partitionCheck (leaves S) P = true) (heT : pairwiseEmbeddings T P = true)
 (heS : pairwiseEmbeddings S P = true) (xm : X ∈ P) (size : 3 ≤ X.length)
 (ha : agreement T S F = true) :
 ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧ Refines G P := by
 have translate {G : List (List Nat)} (ref : Refines G (pendantPartition T p q)) : Refines G P := by
   intro B hB
   obtain ⟨C,hC,bc⟩ := ref B hB
   obtain ⟨D,hD,cd⟩ := mapP C hC
   exact ⟨D,hD,fun x hx => cd (bc x hx)⟩
 have outside : ∀ z, z ∈ leaves T → z ∉ X → ∃ r, r ∈ cuts T p q ∧ z ∈ subtreeLabels T r := by
   intro z hz nz
   apply Classical.byContradiction
   intro no
   exact nz ((core z).1 ((mem_core T p q z).2 ⟨hz,fun r hr zr => no ⟨r,hr,zr⟩⟩))
 have href := translate (splitTwo_refines cutEq (agreement_symm ha))
 have mixedCase (B : List Nat) (hB : B ∈ F) (mix : BinaryExchange.mixed B X.contains = true) :
   ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧ Refines G P := by
   obtain ⟨⟨x,xB,xX⟩,⟨z,zB,zX⟩⟩ := (BinaryExchange.mixed_iff B _).1 mix
   have hx : x ∈ X := List.contains_iff_mem.1 xX
   have hz : z ∉ X := by simpa using zX
   have result := mixed_split_merge_saves hnT hnS hU hxU hV cat ch good outside hp heT heS xm size
     ha cutEq href hB xB zB hx hz
   exact ⟨_,result⟩
 have nonmixed (none : ¬∃ B, B ∈ F ∧ BinaryExchange.mixed B X.contains = true) :
   (splitTwo F T u v).length ≤ F.length+1 := by
   apply no_mixed_core_split_saving hnT (agreement_symm ha) cutEq
   intro C hC x y xC yC xc
   apply (core y).2
   apply Classical.byContradiction
   intro ny
   exact none ⟨C,hC,(BinaryExchange.mixed_iff C _).2
     ⟨⟨x,xC,by simpa using (core x).1 xc⟩,⟨y,yC,by simpa using ny⟩⟩⟩
 rcases actual_pendant_safety hnT (agreement_symm ha) cpq with sp | sq | ref
 · by_cases ex : ∃ B, B ∈ F ∧ BinaryExchange.mixed B X.contains = true
   · obtain ⟨B,hB,hm⟩ := ex; exact mixedCase B hB hm
   · obtain ⟨G,hG,hlen,hrefG⟩ := actual_hard2_exchange_from_split_saving hnS hnT
       (fun x => (same x).symm) (agreement_symm ha) cpq cutEq sp (nonmixed ex)
     exact ⟨G,agreement_symm hG,hlen,translate hrefG⟩
 · by_cases ex : ∃ B, B ∈ F ∧ BinaryExchange.mixed B X.contains = true
   · obtain ⟨B,hB,hm⟩ := ex; exact mixedCase B hB hm
   · obtain ⟨G,hG,hlen,hrefG⟩ := actual_hard2_exchange_from_split_saving_b hnS hnT
       (fun x => (same x).symm) (agreement_symm ha) cpq cutEq sq (nonmixed ex)
     exact ⟨G,agreement_symm hG,hlen,translate hrefG⟩
 · exact ⟨F,ha,Nat.le_refl _,translate ref⟩

end Universal233.Rule5Classification
