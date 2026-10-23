import LocalSelector
namespace Universal233.Rule5FinalClassification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification

theorem admitted_noRule4 {T S : Tree} {a b : Nat} (h : admitted T S a b = true) :
 rule4 T S = false ∧ rule4 S T = false := by
 simp only [admitted,Bool.and_eq_true,beq_iff_eq] at h
 constructor
 · have hh := h.1.1.1.1.1.2
   cases e : rule4 T S <;> simp_all
 · have hh := h.1.1.1.1.2
   cases e : rule4 S T <;> simp_all

theorem remaining_good_pendant_singleton {T S : Tree} {a b : Nat} {e : RMAF.Vertex}
 (h : selectLocal T S a b = some .remaining) (he : e ∈ cuts S a b)
 (hg : restrictionAgrees T S (subtreeLabels S e) = true) :
 ∃ c, subtree S e = some (.leaf c) ∧ subtreeLabels S e = [c] := by
 have sc := selectLocal_cases h
 obtain ⟨U,hU⟩ := ((cuts_spec S a b e).1 he).1
 have pos : 0 < (subtreeLabels S e).length := by
   rw [source_subtree_labels hU]; exact leaves_length_positive U
 have nl : ¬3 ≤ (subtreeLabels S e).length := by
   intro hh
   obtain ⟨d,hd⟩ := selectLarge_complete he hg hh
   rw [sc.2.1] at hd; contradiction
 have nt : (subtreeLabels S e).length ≠ 2 := by
   intro hh
   obtain ⟨d,hd⟩ := sizeTwo_selector_complete he hg hh
   rw [sc.2.2.1] at hd; contradiction
 obtain ⟨c,rfl⟩ := leaves_one_leaf (T:=U) (by rw [←source_subtree_labels hU]; omega)
 exact ⟨c,hU,by rw [source_subtree_labels hU]; rfl⟩

theorem hasCherry_bool {T : Tree} {p : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T p a b) : hasCherry T a b = true := by
 apply List.any_eq_true.2
 exact ⟨(p,a,b),cherries_complete T p a b ch,by simp⟩

theorem cherry_cuts_nil {T : Tree} {a b : Nat} (hn : (leaves T).Nodup)
 (ch : HasCherry a b T) : cuts T a b = [] := by
 induction ch with
 | here => simp [cuts,pendantOriginal,vertices,minimalVertices,rootedSpan,prependSide,leaves]
 | swap => simp [cuts,pendantOriginal,vertices,minimalVertices,rootedSpan,prependSide,leaves,Bool.or_comm]
 | @left l r ch ih =>
   obtain ⟨hnl,hnr,dj⟩ := List.nodup_append.1 hn
   have labs := hasCherry_labels ch
   have ar : a ∉ leaves r := fun h => dj a labs.1 a h rfl
   have br : b ∉ leaves r := fun h => dj b labs.2 b h rfl
   have sp := pairSpan_left labs.1 labs.2 ar br
   have nil := ih hnl
   apply List.eq_nil_iff_forall_not_mem.2
   intro q hq
   have hs := (cuts_spec _ _ _ _).1 hq
   cases q with
   | nil => exact hs.2.1 rfl
   | cons s q =>
     cases q with
     | nil => simpa [sp,prependSide] using hs.2.2.1
     | cons z q =>
       cases s
       · have hc : z::q ∈ cuts l a b := (cuts_spec _ _ _ _).2
           ⟨hs.1,by simp,by simpa [sp,prependSide] using hs.2.2.1,by simpa [sp,prependSide] using hs.2.2.2⟩
         rw [nil] at hc; contradiction
       · simpa [sp,prependSide] using hs.2.2.1
 | @right l r ch ih =>
   obtain ⟨hnl,hnr,dj⟩ := List.nodup_append.1 hn
   have labs := hasCherry_labels ch
   have al : a ∉ leaves l := fun h => dj a h a labs.1 rfl
   have bl : b ∉ leaves l := fun h => dj b h b labs.2 rfl
   have sp := pairSpan_right labs.1 labs.2 al bl
   have nil := ih hnr
   apply List.eq_nil_iff_forall_not_mem.2
   intro q hq
   have hs := (cuts_spec _ _ _ _).1 hq
   cases q with
   | nil => exact hs.2.1 rfl
   | cons s q =>
     cases q with
     | nil => simpa [sp,prependSide] using hs.2.2.1
     | cons z q =>
       cases s
       · simpa [sp,prependSide] using hs.2.2.1
       · have hc : z::q ∈ cuts r a b := (cuts_spec _ _ _ _).2
           ⟨hs.1,by simp,by simpa [sp,prependSide] using hs.2.2.1,by simpa [sp,prependSide] using hs.2.2.2⟩
         rw [nil] at hc; contradiction

theorem noRule4_forbids_singleton_mate {T S : Tree} {i e : RMAF.Vertex} {a b c : Nat}
 (ch : CherryAt T i a b) (hc : (cuts S a b).length = 2)
 (he : e ∈ cuts S a b) (hs : subtreeLabels S e = [c])
 (no : rule4 T S = false) : ¬(HasCherry a c S ∨ HasCherry b c S) := by
 intro hh
 have mate : hasCherry S a c = true ∨ hasCherry S b c = true := by
   rcases hh with h | h
   · obtain ⟨p,h | h⟩ := hasCherry_actual h
     · exact Or.inl (hasCherry_bool h)
     · have h0 := hasCherry_bool h
       unfold hasCherry at h0 ⊢
       left
       simpa only [Bool.or_comm,Bool.and_comm] using h0
   · obtain ⟨p,h | h⟩ := hasCherry_actual h
     · exact Or.inr (hasCherry_bool h)
     · have h0 := hasCherry_bool h
       right
       unfold hasCherry at h0 ⊢
       simpa only [Bool.or_comm,Bool.and_comm] using h0
 have tr : rule4 T S = true := by
   apply List.any_eq_true.2
   refine ⟨⟨i,a,b,cuts S a b⟩,?_,?_⟩
   · exact List.mem_map.2 ⟨(i,a,b),cherries_complete T i a b ch,rfl⟩
   · simp only [hc,beq_self_eq_true,Bool.true_and]
     apply List.any_eq_true.2
     exact ⟨e,he,by simp only [hs]; rcases mate with h | h <;> simp [h]⟩
 rw [no] at tr; contradiction

def fork (s : Bool) (A B : Tree) : Tree := if s then .node B A else .node A B

theorem fork_first (s : Bool) (A B : Tree) : subtree (fork s A B) [s] = some A := by
 cases s <;> rfl
theorem fork_second (s : Bool) (A B : Tree) : subtree (fork s A B) [!s] = some B := by
 cases s <;> rfl

theorem leaf_parent {T : Tree} {a : Nat} (ha : a ∈ leaves T) :
 T = .leaf a ∨ ∃ p s U, subtree T p = some (fork s (.leaf a) U) := by
 induction T with
 | leaf x =>
   have e : a = x := by simpa [leaves] using ha
   subst x
   exact Or.inl rfl
 | node l r il ir =>
   right
   rcases List.mem_append.1 ha with hl | hr
   · rcases il hl with rfl | ⟨p,s,U,hp⟩
     · exact ⟨[],false,r,rfl⟩
     · exact ⟨false::p,s,U,hp⟩
   · rcases ir hr with rfl | ⟨p,s,U,hp⟩
     · exact ⟨[],true,l,rfl⟩
     · exact ⟨true::p,s,U,hp⟩

theorem fork_mate_labels {S U : Tree} {p : RMAF.Vertex} {s : Bool} {a : Nat}
 (hn : (leaves S).Nodup) (hp : subtree S p = some (fork s (.leaf a) U)) :
 a ∉ leaves U := by
 have nd : (leaves (fork s (.leaf a) U)).Nodup := by
   rw [←source_subtree_labels hp]; exact (subtreeLabels_sublist S p).nodup hn
 cases s
 · exact (List.nodup_cons.1 (by simpa [fork,leaves] using nd)).1
 · have dj := (List.nodup_append.1 (by simpa [fork,leaves] using nd)).2.2
   exact fun h => dj a h a (by simp) rfl

theorem cherry_symm {T : Tree} {a b : Nat} (h : HasCherry a b T) : HasCherry b a T := by
 induction h with
 | here => exact .swap
 | swap => exact .here
 | left _ ih => exact .left ih
 | right _ ih => exact .right ih

/-- The endpoint's original sibling is an original outgoing path arc.
Neither the source edge nor its orientation is postulated as geometry. -/
theorem endpoint_mate_cut {S U : Tree} {p : RMAF.Vertex} {s : Bool} {a b : Nat}
 (hn : (leaves S).Nodup) (hp : subtree S p = some (fork s (.leaf a) U))
 (hb : b ∈ leaves S) (neq : a ≠ b) (nb : b ∉ leaves U) :
 p ++ [!s] ∈ cuts S a b := by
 have aa : LeafAt S (p ++ [s]) a := by
   unfold LeafAt; rw [subtree_append hp]; exact fork_first s _ _
 obtain ⟨v,hv⟩ := leaf_exists hb
 have nv : ¬p ++ [s] <+: v := by
   intro h
   have hmem := (subtreeLabels_prefix S (p++[s]) b).2 ⟨v,hv,h⟩
   have one := source_subtree_labels aa
   rw [one] at hmem
   have e : b = a := by simpa [leaves] using hmem
   exact neq e.symm
 have parent : p ∈ minimalVertices [a,b] S := by
   apply (pair_minimal_path hn aa hv p).2
   simpa using cut_crossing_path (q:=p++[s]) (by simp) List.prefix_rfl nv
 have treeU : subtree S (p++[!s]) = some U := by
   rw [subtree_append hp]; exact fork_second s _ _
 have labelsU : subtreeLabels S (p++[!s]) = leaves U := source_subtree_labels treeU
 have na := fork_mate_labels hn hp
 have outside : p++[!s] ∉ minimalVertices [a,b] S := by
   apply no_selected_subtree_hull (a:=p++[!s]) (u:=p++[!s]) ?_ List.prefix_rfl
   intro x hx
   have e : x = a ∨ x = b := by simpa using hx
   rcases e with rfl | rfl <;> simpa [labelsU] using (by assumption : _ ∉ leaves U)
 exact (cuts_spec _ _ _ _).2 ⟨⟨U,treeU⟩,by simp,by simpa using parent,outside⟩

theorem admitted_source_not_cherry {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ha : admitted T S a b = true) (ch : CherryAt T i a b) : ¬HasCherry a b S := by
 intro hh
 obtain ⟨p,h | h⟩ := hasCherry_actual hh
 · have two := earlierClear_cherry (admitted_parts ha).2.2.1 h
   rw [cherry_cuts_nil (properPair_parts (admitted_parts ha).1).1 (actual_hasCherry ch)] at two
   contradiction
 · have two := earlierClear_cherry (admitted_parts ha).2.2.1 h
   rw [cherry_cuts_nil (properPair_parts (admitted_parts ha).1).1 (cherry_symm (actual_hasCherry ch))] at two
   contradiction

/-- Every noncommon endpoint pair exposes at least one actual endpoint
sibling pendant, in either endpoint and either original sibling orientation. -/
theorem exposed_endpoint_mate {S : Tree} {a b : Nat}
 (hn : (leaves S).Nodup) (ha : a ∈ leaves S) (hb : b ∈ leaves S)
 (neq : a ≠ b) (nc : ¬HasCherry a b S) :
 ∃ p s U x y, ((x=a ∧ y=b) ∨ (x=b ∧ y=a)) ∧
 subtree S p = some (fork s (.leaf x) U) ∧ y ∉ leaves U ∧ p++[!s] ∈ cuts S a b := by
 rcases leaf_parent ha with eq | ⟨p,s,U,hp⟩
 · subst S; simp [leaves] at hb; exact False.elim (neq hb.symm)
 · by_cases nb : b ∈ leaves U
   · rcases leaf_parent nb with eq | ⟨q,t,W,hq⟩
     · subst U
       have cherry : HasCherry a b S := by
         cases s
         · exact actual_hasCherry hp
         · have hh : HasCherry b a S := actual_hasCherry hp
           exact cherry_symm hh
       exact False.elim (nc cherry)
     · have hu : subtree S (p++[!s]) = some U := by rw [subtree_append hp]; exact fork_second s _ _
       have hw : subtree S ((p++[!s])++q) = some (fork t (.leaf b) W) := by rw [subtree_append hu]; exact hq
       have nw : a ∉ leaves W := by
         intro h
         have ws : leaves W ⊆ leaves U := by
           have hwu : subtree U (q++[!t]) = some W := by rw [subtree_append hq]; exact fork_second t _ _
           rw [←source_subtree_labels hwu]; exact (subtreeLabels_sublist U _).subset
         exact fork_mate_labels hn hp (ws h)
       have cut := endpoint_mate_cut hn hw ha neq.symm nw
       rw [cuts,pendantOriginal_swap S b a] at cut
       exact ⟨(p++[!s])++q,t,W,b,a,Or.inr ⟨rfl,rfl⟩,hw,nw,cut⟩
   · exact ⟨p,s,U,a,b,Or.inl ⟨rfl,rfl⟩,hp,nb,endpoint_mate_cut hn hp hb neq nb⟩

theorem remaining_exposed_bad {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b = some .remaining) :
 ∃ p s U x y, ((x=a ∧ y=b) ∨ (x=b ∧ y=a)) ∧
 subtree S p = some (fork s (.leaf x) U) ∧ y ∉ leaves U ∧
 p++[!s] ∈ cuts S a b ∧ restrictionAgrees T S (subtreeLabels S (p++[!s])) = false := by
 have facts := selectLocal_cases sel
 have parts := admitted_parts facts.1
 have proper := properPair_parts parts.1
 have aT := leafAt_label T _ a (cherry_left ch)
 have bT := leafAt_label T _ b (cherry_right ch)
 have neq : a ≠ b := by
   intro eq
   have uniq := leaf_unique proper.1 (cherry_left ch) (eq ▸ cherry_right ch)
   simp at uniq
 obtain ⟨p,s,U,x,y,xy,hp,ny,cut⟩ := exposed_endpoint_mate proper.2.1
   ((proper.2.2 a).1 aT) ((proper.2.2 b).1 bT) neq (admitted_source_not_cherry facts.1 ch)
 refine ⟨p,s,U,x,y,xy,hp,ny,cut,?_⟩
 cases good : restrictionAgrees T S (subtreeLabels S (p++[!s])) with
 | false => rfl
 | true =>
   obtain ⟨c,hc,cl⟩ := remaining_good_pendant_singleton sel cut good
   have su : subtree S (p++[!s]) = some U := by rw [subtree_append hp]; exact fork_second s _ _
   have eu : U = .leaf c := Option.some.inj (su.symm.trans hc)
   subst U
   have mate : HasCherry x c S := by
     cases s
     · exact actual_hasCherry hp
     · exact cherry_symm (actual_hasCherry hp)
   have forbidden := noRule4_forbids_singleton_mate ch parts.2.2.2.2 cut cl (admitted_noRule4 facts.1).1
   rcases xy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
   · exact False.elim (forbidden (Or.inl mate))
   · exact False.elim (forbidden (Or.inr mate))

/-- Exact first remaining source statuses. The bad pendant is obtained from
an original endpoint sibling; the other singleton and good core are derived
from the actual three-part good count, rather than certificate fields. -/
theorem remaining_source_status {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b = some .remaining) :
 ∃ e f c, (cuts S a b = [e,f] ∨ cuts S a b = [f,e]) ∧
 restrictionAgrees T S (subtreeLabels S e) = false ∧
 subtree S f = some (.leaf c) ∧ subtreeLabels S f = [c] ∧
 restrictionAgrees T S (coreLabels S a b) = true := by
 have facts := selectLocal_cases sel
 have parts := admitted_parts facts.1
 obtain ⟨p,s,U,x,y,xy,hp,ny,cut,bad⟩ := remaining_exposed_bad ch sel
 obtain ⟨u,v,eq⟩ := list_two_named (cuts S a b) parts.2.2.2.2
 have epart : p++[!s] = u ∨ p++[!s] = v := by simpa [eq] using cut
 have goodcount : ((pendantPartition S a b).filter (restrictionAgrees T S)).length = 2 := by
   have hh := facts.1
   simp only [admitted,Bool.and_eq_true,beq_iff_eq] at hh
   exact hh.2
 have gg {e f : RMAF.Vertex} (cutsEq : cuts S a b = [e,f])
  (bad : restrictionAgrees T S (subtreeLabels S e) = false) :
  restrictionAgrees T S (subtreeLabels S f) = true ∧ restrictionAgrees T S (coreLabels S a b) = true := by
   simp only [pendantPartition,cutsEq,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
     List.filter_cons,bad,Bool.false_eq_true,↓reduceIte] at goodcount
   cases hf : restrictionAgrees T S (subtreeLabels S f) <;>
    cases hg : restrictionAgrees T S (coreLabels S a b) <;> simp_all
 rcases epart with ep | ep
 · have bg : restrictionAgrees T S (subtreeLabels S u) = false := ep ▸ bad
   obtain ⟨gf,gc⟩ := gg eq bg
   obtain ⟨c,hc,cl⟩ := remaining_good_pendant_singleton sel (by simp [eq]) gf
   exact ⟨u,v,c,Or.inl eq,bg,hc,cl,gc⟩
 · have bg : restrictionAgrees T S (subtreeLabels S v) = false := ep ▸ bad
   have count : restrictionAgrees T S (subtreeLabels S u) = true ∧ restrictionAgrees T S (coreLabels S a b) = true := by
     simp only [pendantPartition,eq,List.map_cons,List.map_nil,List.cons_append,List.nil_append] at goodcount
     cases hf : restrictionAgrees T S (subtreeLabels S u) <;>
      cases hg : restrictionAgrees T S (coreLabels S a b) <;> simp_all
   obtain ⟨c,hc,cl⟩ := remaining_good_pendant_singleton sel (by simp [eq]) count.1
   exact ⟨v,u,c,Or.inr eq,bg,hc,cl,count.2⟩

theorem remaining_source_core {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b = some .remaining) :
 ∃ U, restrict (coreLabels S a b) S = some U ∧ Caterpillar U ∧
 (cherries U).length = 1 ∧ HasCherry a b U := by
 have facts := selectLocal_cases sel
 have proper := properPair_parts (admitted_parts facts.1).1
 have aS := (proper.2.2 a).1 (leafAt_label T _ a (cherry_left ch))
 have bS := (proper.2.2 b).1 (leafAt_label T _ b (cherry_right ch))
 have neq : a ≠ b := by
   intro eq
   have uniq := leaf_unique proper.1 (cherry_left ch) (eq ▸ cherry_right ch)
   simp at uniq
 obtain ⟨U,hU,cu⟩ := core_has_cherry proper.2.1 aS bS neq
 obtain ⟨e,f,c,cut,bad,hc,cl,gc⟩ := remaining_source_status ch sel
 have cat := no_outside_core_caterpillar proper.2.1 aS bS neq hU gc facts.2.2.2
 exact ⟨U,hU,cat.1,cat.2,cu⟩

end Universal233.Rule5FinalClassification
