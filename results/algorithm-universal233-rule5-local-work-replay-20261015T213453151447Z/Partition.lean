import Ordinary
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

theorem pendant_flat_nodup {S : Tree} {a b : Nat} (hn : (leaves S).Nodup)
 (qs : List RMAF.Vertex) (hq : ∀ q, q ∈ qs → q ∈ cuts S a b) (hnd : qs.Nodup) :
 (qs.map (subtreeLabels S)).flatten.Nodup := by
 induction qs with
 | nil => simp
 | cons q qs ih =>
   have hh := List.nodup_cons.1 hnd
   simp only [List.map_cons,List.flatten_cons]
   apply List.nodup_append.2
   refine ⟨(subtreeLabels_sublist S q).nodup hn,
     ih (fun r hr => hq r (by simp [hr])) hh.2,?_⟩
   intro x hx y hy e
   subst y
   obtain ⟨L,hL,hxL⟩ := List.mem_flatten.1 hy
   obtain ⟨r,hr,he⟩ := List.mem_map.1 hL
   subst L
   exact pendant_labelsets_disjoint hn (hq q (by simp)) (hq r (by simp [hr]))
     (fun e => hh.1 (e ▸ hr)) x hx hxL

theorem pendant_partition_check {S : Tree} {a b : Nat}
 (hn : (leaves S).Nodup) (ha : a ∈ leaves S) :
 partitionCheck (leaves S) (pendantPartition S a b) = true := by
 let X := ((cuts S a b).map (subtreeLabels S)).flatten
 let C := coreLabels S a b
 have hX : X.Nodup := pendant_flat_nodup hn _ (fun _ h => h) (pendantOriginal_nodup S a b)
 have hC : C.Nodup := hn.filter _
 have countone : ∀ x, x ∈ leaves S → (X ++ C).count x = 1 := by
   intro x hx
   by_cases hm : x ∈ X
   · have hc : x ∉ C := by simp [C,coreLabels,X,hm]
     simp [List.count_append,hX.count,hC.count,hm,hc]
   · have hc : x ∈ C := by simp [C,coreLabels,X,hx,hm]
     simp [List.count_append,hX.count,hC.count,hm,hc]
 simp only [partitionCheck,Bool.and_eq_true]
 refine ⟨⟨?_,?_⟩,?_⟩
 · apply List.all_eq_true.2
   intro B hB
   have casesB : (∃ q, q ∈ cuts S a b ∧ subtreeLabels S q = B) ∨ B = C := by
     simpa [pendantPartition,C] using hB
   have hne : B ≠ [] := by
     rcases casesB with ⟨q,hq,rfl⟩ | rfl
     · exact subtreeLabels_nonempty ((cuts_spec S a b q).1 hq).1
     · intro he
       have hh : a ∈ C := endpoint_core (Or.inl rfl) ha
       rw [he] at hh; exact List.not_mem_nil hh
   cases B with
   | nil => contradiction
   | cons x xs => rfl
 · apply List.all_eq_true.2
   intro x hx
   apply beq_iff_eq.2
   simpa [pendantPartition,X,C] using countone x hx
 · apply List.all_eq_true.2
   intro x hx
   apply List.contains_iff_mem.2
   have hxc : x ∈ X ∨ x ∈ C := by simpa [pendantPartition,X,C] using hx
   rcases hxc with h | h
   · obtain ⟨L,hL,hxL⟩ := List.mem_flatten.1 h
     obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hL
     exact (subtreeLabels_sublist S q).subset hxL
   · exact (List.mem_filter.1 h).1

theorem path_prefix_closed (q : RMAF.Vertex) {v u w : RMAF.Vertex}
 (hu : q <+: u) (hw : q <+: w) (hp : PathAt v u w) : q <+: v := by
 induction q generalizing v u w with
 | nil => exact List.nil_prefix
 | cons s q ih =>
   obtain ⟨ut,rfl⟩ := hu
   obtain ⟨wt,rfl⟩ := hw
   cases v with
   | nil => exact False.elim (path_root_same_impossible s _ _ hp)
   | cons t v =>
     by_cases e : t = s
     · subst t
       have hh := ih (List.prefix_append _ _) (List.prefix_append _ _)
         ((path_same_side s _ _ _).1 hp)
       rcases hh with ⟨tail,he⟩
       exact ⟨tail,by simpa using congrArg (s :: ·) he⟩
     · have he : s = !t := by cases s <;> cases t <;> simp_all
       rw [he] at hp
       exact False.elim (path_other_same_impossible t _ _ _ hp)

theorem path_root_prefix {v u : RMAF.Vertex} (hp : PathAt v u []) : v <+: u := by
 induction v generalizing u with
 | nil => exact List.nil_prefix
 | cons s v ih =>
   cases u with
   | nil => have he := path_identical (s::v) [] hp; simp at he
   | cons t u =>
     by_cases e : t = s
     · subst t
       obtain ⟨tail,he⟩ := ih ((path_same_side_to_root s v u).1 hp)
       exact ⟨tail,by simpa using congrArg (s :: ·) he⟩
     · have he : t = !s := by cases s <;> cases t <;> simp_all
       rw [he] at hp
       exact False.elim (path_other_to_root_impossible s _ _ hp)

theorem subtree_hull {S : Tree} (hn : (leaves S).Nodup) (q v : RMAF.Vertex)
 (hv : v ∈ minimalVertices (subtreeLabels S q) S) : q <+: v := by
 obtain ⟨u,w,hu,hw,hp⟩ := (minimalVertices_correct _ S v).1 hv
 have one : ∀ u, selectedLeaves (subtreeLabels S q) S u → q <+: u := by
   intro u hu
   obtain ⟨x,hx,hux⟩ := (selected_decompose_label _ S u).1 hu
   obtain ⟨w,hw,hqw⟩ := (subtreeLabels_prefix S q x).1 hx
   exact (leaf_unique hn hw ((leafAt_selected S u x).2 hux)) ▸ hqw
 exact path_prefix_closed q (one u hu) (one w hw) hp

theorem core_hull {S : Tree} {a b : Nat} (hn : (leaves S).Nodup)
 (v : RMAF.Vertex) (hv : v ∈ minimalVertices (coreLabels S a b) S) :
 Live (cuts S a b) v := by
 obtain ⟨u,hu,hp⟩ := hull_subset_reach _ v ((minimalVertices_correct _ S v).1 hv)
 obtain ⟨x,hx,hux⟩ := (selected_decompose_label _ S u).1 hu
 intro q hq hqv
 exact ((mem_core S a b x).1 hx).2 q hq
   ((subtreeLabels_prefix S q x).2 ⟨u,(leafAt_selected S u x).2 hux,
     hqv.trans (path_root_prefix hp)⟩)

def rootBlock (S : Tree) (a b : Nat) (r : RMAF.Vertex) : List Nat :=
 if r = [] then coreLabels S a b else subtreeLabels S r

theorem root_map (S : Tree) (a b : Nat) :
 (componentRoots S a b).map (rootBlock S a b) = pendantPartition S a b := by
 simp only [componentRoots,List.map_append,List.map_cons,List.map_nil,rootBlock,ite_true]
 congr 1
 apply List.map_congr_left
 intro r hr
 simp [rootBlock,((cuts_spec S a b r).1 hr).2.1]

theorem block_hull_region {S : Tree} {a b : Nat} (hn : (leaves S).Nodup)
 {r v : RMAF.Vertex} (hr : r ∈ componentRoots S a b)
 (hv : v ∈ minimalVertices (rootBlock S a b r) S) : Region (cuts S a b) r v := by
 by_cases e : r = []
 · subst r
   rw [region_root _ _ (fun q hq => ((cuts_spec S a b q).1 hq).2.1)]
   exact core_hull hn v (by simpa [rootBlock] using hv)
 · have hm : r ∈ cuts S a b := by simpa [componentRoots,e] using hr
   exact (pendant_region hm).2 (subtree_hull hn r v (by simpa [rootBlock,e] using hv))

theorem source_embeddings {S : Tree} {a b : Nat} (hn : (leaves S).Nodup) :
 pairwiseEmbeddings S (pendantPartition S a b) = true := by
 have hroots : (componentRoots S a b).Nodup := by
   simp only [componentRoots,List.nodup_append]
   exact ⟨pendantOriginal_nodup S a b,by simp,by
     intro q hq z hz; simp only [List.mem_singleton] at hz; subst z
     exact ((cuts_spec S a b q).1 hq).2.1⟩
 rw [←root_map S a b,executable_pairwiseEmbeddings,List.pairwise_map]
 apply List.Pairwise.imp_of_mem (p := hroots)
 intro r s hr hs hne v ⟨hv,hw⟩
 have rr : r = [] ∨ r ∈ cuts S a b := by simpa [componentRoots,or_comm] using hr
 have ss : s = [] ∨ s ∈ cuts S a b := by simpa [componentRoots,or_comm] using hs
 exact hne (rooted_regions_disjoint rr ss
   (block_hull_region hn hr ((minimalVertices_correct _ S v).2 hv))
   (block_hull_region hn hs ((minimalVertices_correct _ S v).2 hw)))
end Universal233.CherryBranching
