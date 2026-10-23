import FinalSelector
namespace Universal233.Rule5FinalClassification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification

theorem subtree_parent_fork {S A : Tree} {p : RMAF.Vertex} {b : Nat}
 (hp : subtree S p = some A) (hb : b ∈ leaves S) (nb : b ∉ leaves A) :
 ∃ g s W, p=g++[s] ∧ subtree S g = some (fork s A W) := by
 have pn : p≠[] := by
   intro eq; subst p
   have eq : S=A := Option.some.inj hp
   subst A; contradiction
 rcases List.eq_nil_or_concat p with eq | ⟨g,s,eq⟩
 · contradiction
 · simp only [List.concat_eq_append] at eq
   obtain ⟨G,hg⟩ := valid_ancestor ⟨A,hp⟩ (eq ▸ List.prefix_append g [s])
   have child : subtree G [s] = some A := by rw [←subtree_append hg,←eq]; exact hp
   cases G with
   | leaf x => simp [subtree] at child
   | node l r =>
     cases s
     · have ea : l=A := Option.some.inj child
       subst l; exact ⟨g,false,r,eq,hg⟩
     · have ea : r=A := Option.some.inj child
       subst r; exact ⟨g,true,l,eq,hg⟩

theorem general_mate_cut {S A W : Tree} {g : RMAF.Vertex} {s : Bool} {a b : Nat}
 (hn : (leaves S).Nodup) (hg : subtree S g = some (fork s A W))
 (ha : a ∈ leaves A) (hb : b ∈ leaves S) (nA : b ∉ leaves A) (nW : b ∉ leaves W) :
 g++[!s] ∈ cuts S a b := by
 have htA : subtree S (g++[s]) = some A := by rw [subtree_append hg]; exact fork_first s _ _
 have htW : subtree S (g++[!s]) = some W := by rw [subtree_append hg]; exact fork_second s _ _
 obtain ⟨u,hu⟩ := leaf_exists ha
 have au : LeafAt S ((g++[s])++u) a := by unfold LeafAt; rw [subtree_append htA]; exact hu
 obtain ⟨v,hv⟩ := leaf_exists hb
 have nv : ¬g++[s] <+: v := by
   intro pre
   exact nA (by rw [←source_subtree_labels htA]; exact (subtreeLabels_prefix S _ b).2 ⟨v,hv,pre⟩)
 have parent : g ∈ minimalVertices [a,b] S := by
   apply (pair_minimal_path hn au hv g).2
   simpa using cut_crossing_path (q:=g++[s]) (by simp) (List.prefix_append _ _) nv
 have nd : (leaves (fork s A W)).Nodup := by
   rw [←source_subtree_labels hg]; exact (subtreeLabels_sublist S g).nodup hn
 have dis := (fork_nodup_parts nd).2.2
 have nWa : a ∉ leaves W := dis a ha
 have out : g++[!s] ∉ minimalVertices [a,b] S := by
   apply no_selected_subtree_hull (a:=g++[!s]) (u:=g++[!s]) ?_ List.prefix_rfl
   intro x hx
   have xx : x=a ∨ x=b := by simpa using hx
   rw [source_subtree_labels htW]
   rcases xx with rfl | rfl <;> assumption
 exact (cuts_spec _ _ _ _).2 ⟨⟨W,htW⟩,by simp,by simpa using parent,out⟩

/-- Every original core label below an actual path vertex is an endpoint.
This consumes the literal source cut definition through its first exit. -/
theorem core_below_path_only {S : Tree} {g : RMAF.Vertex} {a b x : Nat}
 (hg : g ∈ minimalVertices [a,b] S) (hx : x ∈ coreLabels S a b)
 (xg : x ∈ subtreeLabels S g) : x=a ∨ x=b := by
 by_cases eq : x=a ∨ x=b
 · exact eq
 · obtain ⟨v,hv,gv⟩ := (subtreeLabels_prefix S g x).1 xg
   obtain ⟨tail,et⟩ := gv
   have off : v ∉ minimalVertices [a,b] S := by
     rw [minimalVertices_terminal [a,b] S v x hv]
     simpa using eq
   have endOff : ¬(g++tail ∈ minimalVertices [a,b] S) := et ▸ off
   obtain ⟨q,qn,qt,qp,qo⟩ := first_exit (fun u => g++u ∈ minimalVertices [a,b] S) tail
     (by simpa using hg) endOff
   have pre : g++q <+: v := by
     obtain ⟨u,eu⟩ := qt
     exact ⟨u,by rw [List.append_assoc,eu,et]⟩
   have valid : Valid S (g++q) := valid_ancestor hv.valid pre
   have cut : g++q ∈ cuts S a b := (cuts_spec _ _ _ _).2
     ⟨valid,by intro e; have ln := congrArg List.length e; simp at ln; exact qn ln.2,
       by rw [List.dropLast_append_of_ne_nil qn]; exact qp,qo⟩
   exact False.elim (((mem_core S a b x).1 hx).2 (g++q) cut
     ((subtreeLabels_prefix S _ x).2 ⟨v,hv,pre⟩))

theorem hull_under_both {S : Tree} {g v : RMAF.Vertex} {a b : Nat}
 (hn : (leaves S).Nodup) (ha : a∈subtreeLabels S g) (hb : b∈subtreeLabels S g)
 (hv : v∈minimalVertices [a,b] S) : g <+: v := by
 apply subtree_hull hn g v
 exact executable_span_monotone S [a,b] (subtreeLabels S g)
   (by intro x hx; have eq : x=a ∨ x=b := by simpa using hx
       rcases eq with rfl | rfl <;> assumption) v hv

theorem singleton_agrees {T S : Tree} {c : Nat} (hT : (leaves T).Nodup) (hS : (leaves S).Nodup)
 (cT : c∈leaves T) (cS : c∈leaves S) : restrictionAgrees T S [c] = true := by
 have rt := restrict_only_leaf hT cT (by simp : c∈[c]) (by intro x hx hm; simpa using hm)
 have rs := restrict_only_leaf hS cS (by simp : c∈[c]) (by intro x hx hm; simpa using hm)
 simp [restrictionAgrees,rt,rs,sameShape]

theorem remaining_exposed_full {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b = some .remaining) :
 ∃ p s U x y f c, ((x=a ∧ y=b) ∨ (x=b ∧ y=a)) ∧
 subtree S p = some (fork s (.leaf x) U) ∧ y ∉ leaves U ∧
 (cuts S a b = [p++[!s],f] ∨ cuts S a b = [f,p++[!s]]) ∧
 restrictionAgrees T S (subtreeLabels S (p++[!s])) = false ∧
 subtree S f = some (.leaf c) ∧ restrictionAgrees T S (coreLabels S a b) = true := by
 have proper := properPair_parts (admitted_parts (selectLocal_cases sel).1).1
 obtain ⟨p,s,U,x,y,xy,hp,ny,em,bad⟩ := remaining_exposed_bad ch sel
 obtain ⟨e,f,c,eq,be,hf,cl,gc⟩ := remaining_source_status ch sel
 have cS := leafAt_label S f c hf
 have gf : restrictionAgrees T S (subtreeLabels S f) = true := by
   rw [cl]; exact singleton_agrees proper.1 proper.2.1 ((proper.2.2 c).2 cS) cS
 have ee : p++[!s] = e := by
   have choice : p++[!s]=e ∨ p++[!s]=f := by rcases eq with eq | eq <;> simpa [eq,or_comm] using em
   rcases choice with hh | hh
   · exact hh
   · rw [hh,gf] at bad; contradiction
 exact ⟨p,s,U,x,y,f,c,xy,hp,ny,by simpa [ee] using eq,bad,hf,gc⟩

theorem opposite_child_not_prefix (g : RMAF.Vertex) (s : Bool) (u v : RMAF.Vertex) :
 ¬g++[s]++u <+: g++[!s]++v := by
 rintro ⟨tail,eq⟩
 have hh : s::(u++tail)=(!s)::v := by
   apply List.append_cancel_left (as:=g)
   simpa [List.append_assoc] using eq
 have hh := (List.cons.inj hh).1
 cases s <;> simp at hh

theorem fork_path_root {S A W : Tree} {g : RMAF.Vertex} {s : Bool} {a b : Nat}
 (hn : (leaves S).Nodup) (hg : subtree S g = some (fork s A W))
 (ha : a∈leaves A) (hb : b∈leaves W) : g∈minimalVertices [a,b] S := by
 obtain ⟨u,hu⟩ := leaf_exists ha
 obtain ⟨v,hv⟩ := leaf_exists hb
 have ta : subtree S (g++[s]) = some A := by rw [subtree_append hg]; exact fork_first s _ _
 have tb : subtree S (g++[!s]) = some W := by rw [subtree_append hg]; exact fork_second s _ _
 have au : LeafAt S ((g++[s])++u) a := by unfold LeafAt; rw [subtree_append ta]; exact hu
 have bv : LeafAt S ((g++[!s])++v) b := by unfold LeafAt; rw [subtree_append tb]; exact hv
 apply (pair_minimal_path hn au bv g).2
 have path : PathAt [] (s::u) ((!s)::v) := by cases s <;> constructor
 simpa [List.append_assoc] using path_prepend g path

theorem core_of_neither_pendant {S : Tree} {a b x c : Nat} {e f : RMAF.Vertex}
 (cut : cuts S a b=[e,f] ∨ cuts S a b=[f,e]) (hf : subtree S f=some (.leaf c))
 (xs : x∈leaves S) (nx : x∉subtreeLabels S e) (nc : x≠c) : x∈coreLabels S a b := by
 have cl : subtreeLabels S f=[c] := source_subtree_labels hf
 apply (mem_core S a b x).2
 refine ⟨xs,?_⟩
 intro q qm
 have qe : q=e ∨ q=f := by rcases cut with eq | eq <;> simpa [eq,or_comm] using qm
 rcases qe with rfl | rfl
 · exact nx
 · simpa [cl] using nc

theorem two_label_tree {W : Tree} {b c : Nat} (hn : (leaves W).Nodup)
 (bW : b∈leaves W) (cW : c∈leaves W) (ne : b≠c)
 (only : ∀ z, z∈leaves W → z=b ∨ z=c) :
 W=.node (.leaf b) (.leaf c) ∨ W=.node (.leaf c) (.leaf b) := by
 have le := hn.length_le_of_subset (l₂:=[b,c]) (by intro z hz; simpa using only z hz)
 have lo : 2≤(leaves W).length := by
   have nd : ([b,c] : List Nat).Nodup := by simp [ne]
   exact nd.length_le_of_subset (by
     intro z hz
     have hh : z=b ∨ z=c := by simpa using hz
     rcases hh with rfl | rfl <;> assumption)
 obtain ⟨p,q,eq⟩ := leaves_two_cherry (T:=W) (by simp only [List.length_cons,List.length_nil] at le; omega)
 subst W
 have pb : b=p ∨ b=q := by simpa [leaves] using bW
 have pc : c=p ∨ c=q := by simpa [leaves] using cW
 rcases pb with rfl | rfl <;> rcases pc with rfl | rfl
 · contradiction
 · exact Or.inl rfl
 · exact Or.inr rfl
 · contradiction

theorem fork_mem (s : Bool) (A B : Tree) (x : Nat) :
 x∈leaves (fork s A B) ↔ x∈leaves A ∨ x∈leaves B := by
 cases s <;> simp [fork,leaves,or_comm]

/-- The actual two source arcs and the literal no-Rule4 cherry exclusion
force the three forks below the a,b LCA. All fork orientations are retained. -/
theorem source_two_pendant_spine {S U : Tree} {p f : RMAF.Vertex} {s : Bool} {a b c : Nat}
 (hn : (leaves S).Nodup) (ha : a∈leaves S) (hb : b∈leaves S) (nab : a≠b)
 (hp : subtree S p=some (fork s (.leaf a) U)) (nU : b∉leaves U)
 (cut : cuts S a b=[p++[!s],f] ∨ cuts S a b=[f,p++[!s]])
 (hf : subtree S f=some (.leaf c)) (forbid : ¬HasCherry b c S) :
 ∃ h t r, subtree S h=some (fork r (fork t (fork s (.leaf a) U) (.leaf c)) (.leaf b)) := by
 let e := p++[!s]
 let A := fork s (.leaf a) U
 have htU : subtree S e=some U := by rw [subtree_append hp]; exact fork_second s _ _
 have em : e∈cuts S a b := by rcases cut with eq | eq <;> simp [eq,e]
 have fm : f∈cuts S a b := by rcases cut with eq | eq <;> simp [eq,e]
 have ef : e≠f := by
   have nd : (cuts S a b).Nodup := pendantOriginal_nodup S a b
   rcases cut with eq | eq
   · simpa [eq,e] using nd
   · have fe : f≠e := by simpa [eq,e] using nd
     exact fe.symm
 have cF : c∈subtreeLabels S f := by rw [source_subtree_labels hf]; simp [leaves]
 have nca : c≠a := by
   intro eq
   exact source_label_outside_pendant fm (Or.inl rfl) ha (eq ▸ cF)
 have ncb : c≠b := by
   intro eq
   exact source_label_outside_pendant fm (Or.inr rfl) hb (eq ▸ cF)
 have ncU : c∉leaves U := by
   rw [←source_subtree_labels htU]
   exact pendant_labelsets_disjoint hn fm em ef.symm c cF
 have aA : a∈leaves A := (fork_mem s _ _ _).2 (Or.inl (by simp [leaves]))
 have bA : b∉leaves A := by
   rw [fork_mem]; simp [leaves,nab.symm,nU]
 have cA : c∉leaves A := by rw [fork_mem]; simp [leaves,nca,ncU]
 obtain ⟨g,t,W,pg,hg⟩ := subtree_parent_fork hp hb bA
 have ndG : (leaves (fork t A W)).Nodup := by
   rw [←source_subtree_labels hg]; exact (subtreeLabels_sublist S g).nodup hn
 have disG := (fork_nodup_parts ndG).2.2
 have htW : subtree S (g++[!t])=some W := by rw [subtree_append hg]; exact fork_second t _ _
 have badLeg : ¬b∈leaves W := by
   intro bW
   have root := fork_path_root hn hg aA bW
   have aG : a∈subtreeLabels S g := by rw [source_subtree_labels hg]; exact (fork_mem t _ _ _).2 (Or.inl aA)
   have bG : b∈subtreeLabels S g := by rw [source_subtree_labels hg]; exact (fork_mem t _ _ _).2 (Or.inr bW)
   have cfpre : g <+: f := (hull_under_both hn aG bG ((cuts_spec S a b f).1 fm).2.2.1).trans (List.dropLast_prefix f)
   have cG : c∈subtreeLabels S g :=
     (subtreeLabels_prefix_subset S cfpre) cF
   have cW : c∈leaves W := by
     rw [source_subtree_labels hg,fork_mem] at cG
     exact cG.resolve_left cA
   have only : ∀ z, z∈leaves W → z=b ∨ z=c := by
     intro z zW
     by_cases zc : z=c
     · exact Or.inr zc
     · have nzU : z∉subtreeLabels S e := by
         rw [source_subtree_labels htU]
         intro zU
         have zA : z∈leaves A := (fork_mem s _ _ _).2 (Or.inr zU)
         exact disG z zA zW
       have zS : z∈leaves S := (subtreeLabels_sublist S (g++[!t])).subset (by rw [source_subtree_labels htW]; exact zW)
       have zC := core_of_neither_pendant cut hf zS nzU zc
       have zG : z∈subtreeLabels S g := by rw [source_subtree_labels hg]; exact (fork_mem t _ _ _).2 (Or.inr zW)
       rcases core_below_path_only root zC zG with za | zb
       · exact False.elim (disG a aA (za ▸ zW))
       · exact Or.inl zb
   have pair := two_label_tree (fork_nodup_parts ndG).2.1 bW cW ncb.symm only
   have mate : HasCherry b c S := by
     rcases pair with eq | eq
     · rw [eq] at htW; exact actual_hasCherry htW
     · rw [eq] at htW; exact cherry_symm (actual_hasCherry htW)
   exact forbid mate
 have wm : g++[!t] ∈ cuts S a b := general_mate_cut hn hg aA hb bA badLeg
 have we : g++[!t] ≠ e := by
   intro eq
   have pe : g++[!t] <+: e := ⟨[],by simpa using eq⟩
   have op : ¬g++[!t] <+: g++[t]++[!s] := by simpa using opposite_child_not_prefix g (!t) [] [!s]
   exact op (by simpa [e,pg] using pe)
 have wf : g++[!t]=f := by
   have choices : g++[!t]=e ∨ g++[!t]=f := by rcases cut with eq | eq <;> simpa [eq,e,or_comm] using wm
   exact choices.resolve_left we
 have Wc : W=.leaf c := Option.some.inj (htW.symm.trans (wf ▸ hf))
 subst W
 let G := fork t A (.leaf c)
 have aG : a∈leaves G := (fork_mem t _ _ _).2 (Or.inl aA)
 have bG : b∉leaves G := by rw [fork_mem]; simp [leaves,bA,ncb.symm]
 obtain ⟨h,r,V,gh,hh⟩ := subtree_parent_fork hg hb bG
 have ndH : (leaves (fork r G V)).Nodup := by
   rw [←source_subtree_labels hh]; exact (subtreeLabels_sublist S h).nodup hn
 have disH := (fork_nodup_parts ndH).2.2
 have ePre : g <+: e := by dsimp [e]; rw [pg]; exact ⟨[t,!s],by simp [List.append_assoc]⟩
 have fPre : g <+: f := by rw [←wf]; exact List.prefix_append _ _
 have bV : b∈leaves V := by
   apply Classical.byContradiction
   intro nbV
   have vm := general_mate_cut hn hh aG hb bG nbV
   have no {q : RMAF.Vertex} (pre : g <+: q) : h++[!r] ≠ q := by
     intro eq
     rw [gh] at pre
     obtain ⟨tail,et⟩ := pre
     have none : ¬h++[!r] <+: h++[r]++tail := by simpa using opposite_child_not_prefix h (!r) [] tail
     apply none
     rw [et,←eq]
     exact List.prefix_rfl
   have choices : h++[!r]=e ∨ h++[!r]=f := by rcases cut with eq | eq <;> simpa [eq,e,or_comm] using vm
   exact choices.elim (no ePre) (no fPre)
 have rootH := fork_path_root hn hh aG bV
 have onlyV : ∀ z, z∈leaves V → z=b := by
   intro z zV
   have nzU : z∉subtreeLabels S e := by
     rw [source_subtree_labels htU]
     intro zU
     have zA : z∈leaves A := (fork_mem s _ _ _).2 (Or.inr zU)
     have zG : z∈leaves G := (fork_mem t _ _ _).2 (Or.inl zA)
     exact disH z zG zV
   have zc : z≠c := by
     intro eq
     have cG : c∈leaves G := (fork_mem t _ _ _).2 (Or.inr (by simp [leaves]))
     exact disH c cG (eq ▸ zV)
   have htV : subtree S (h++[!r])=some V := by rw [subtree_append hh]; exact fork_second r _ _
   have zS := (subtreeLabels_sublist S (h++[!r])).subset (by rw [source_subtree_labels htV]; exact zV)
   have zC := core_of_neither_pendant cut hf zS nzU zc
   have zH : z∈subtreeLabels S h := by rw [source_subtree_labels hh]; exact (fork_mem r _ _ _).2 (Or.inr zV)
   rcases core_below_path_only rootH zC zH with za | zb
   · exact False.elim (disH a aG (za ▸ zV))
   · exact zb
 have Vb : V=.leaf b := proper_one_label_tree (fork_nodup_parts ndH).2.1 onlyV
 subst V
 exact ⟨h,t,r,hh⟩

theorem remaining_source_spine {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b = some .remaining) :
 ∃ h p s t r U x y f c, ((x=a ∧ y=b) ∨ (x=b ∧ y=a)) ∧
 subtree S p=some (fork s (.leaf x) U) ∧
 (cuts S a b=[p++[!s],f] ∨ cuts S a b=[f,p++[!s]]) ∧ subtree S f=some (.leaf c) ∧
 restrictionAgrees T S (subtreeLabels S (p++[!s]))=false ∧
 restrictionAgrees T S (coreLabels S a b)=true ∧
 subtree S h=some (fork r (fork t (fork s (.leaf x) U) (.leaf c)) (.leaf y)) := by
 have facts := selectLocal_cases sel
 have part := admitted_parts facts.1
 have proper := properPair_parts part.1
 have aS := (proper.2.2 a).1 (leafAt_label T _ a (cherry_left ch))
 have bS := (proper.2.2 b).1 (leafAt_label T _ b (cherry_right ch))
 have nab : a≠b := by
   intro eq
   have uniq := leaf_unique proper.1 (cherry_left ch) (eq ▸ cherry_right ch)
   simp at uniq
 obtain ⟨p,s,U,x,y,f,c,xy,hp,nU,cut,bad,hf,gc⟩ := remaining_exposed_full ch sel
 have fm : f∈cuts S a b := by rcases cut with eq | eq <;> simp [eq]
 have cl : subtreeLabels S f=[c] := source_subtree_labels hf
 have no := noRule4_forbids_singleton_mate ch part.2.2.2.2 fm cl (admitted_noRule4 facts.1).1
 have out : ∃ h t r, subtree S h=some (fork r (fork t (fork s (.leaf x) U) (.leaf c)) (.leaf y)) := by
   rcases xy with ⟨ex,ey⟩ | ⟨ex,ey⟩
   · subst x; subst y
     exact source_two_pendant_spine proper.2.1 aS bS nab hp nU cut hf (fun h => no (Or.inr h))
   · subst x; subst y
     have swapped : cuts S b a=cuts S a b := pendantOriginal_swap S b a
     have cut' : cuts S b a=[p++[!s],f] ∨ cuts S b a=[f,p++[!s]] := swapped ▸ cut
     exact source_two_pendant_spine proper.2.1 bS aS nab.symm hp nU cut' hf (fun h => no (Or.inl h))
 obtain ⟨h,t,r,hh⟩ := out
 exact ⟨h,p,s,t,r,U,x,y,f,c,xy,hp,cut,hf,bad,gc,hh⟩

theorem outside_original_refusal {T S : Tree} {a b p q : Nat} {j : RMAF.Vertex}
 (none : selectOutside T S a b=none) (good : restrictionAgrees T S (coreLabels S a b)=true)
 (ch : CherryAt S j p q) (pC : p∈coreLabels S a b) (qC : q∈coreLabels S a b)
 (sep : p≠a ∧ p≠b ∧ q≠a ∧ q≠b) : False := by
 have mem : (⟨j,p,q⟩ : OutsideSelection) ∈ outsideCandidates T S a b := by
   apply List.mem_filterMap.2
   exact ⟨(j,p,q),cherries_complete S j p q ch,by simp [outsideAt,good,pC,qC,sep.1,sep.2.1,sep.2.2.1,sep.2.2.2]⟩
 cases eq : outsideCandidates T S a b with
 | nil => rw [eq] at mem; contradiction
 | cons d ds => simp [selectOutside,eq] at none

theorem outside_subtree_leaf {T S W : Tree} {a b : Nat} {q : RMAF.Vertex}
 (none : selectOutside T S a b=none) (good : restrictionAgrees T S (coreLabels S a b)=true)
 (hq : subtree S q=some W) (all : ∀x,x∈leaves W → x∈coreLabels S a b)
 (na : a∉leaves W) (nb : b∉leaves W) : ∃ c,W=.leaf c := by
 cases W with
 | leaf c => exact ⟨c,rfl⟩
 | node l r =>
   obtain ⟨j,p,q',ch⟩ := node_contains_cherry l r
   have global : CherryAt S (q++j) p q' := by unfold CherryAt; rw [subtree_append hq]; exact ch
   have lab := hasCherry_labels (actual_hasCherry ch)
   have sep : p≠a ∧ p≠b ∧ q'≠a ∧ q'≠b :=
     ⟨fun eq => na (eq ▸ lab.1),fun eq => nb (eq ▸ lab.1),fun eq => na (eq ▸ lab.2),fun eq => nb (eq ▸ lab.2)⟩
   exact False.elim (outside_original_refusal none good global (all _ lab.1) (all _ lab.2) sep)

/-- Original ancestor context, retaining each left/right sibling orientation.
Every sibling above the Figure15 LCA is an actual original leaf. -/
inductive LeafContext : Tree → Tree → Prop where
 | here (V) : LeafContext V V
 | left (x) {S V} : LeafContext S V → LeafContext (.node (.leaf x) S) V
 | right (x) {S V} : LeafContext S V → LeafContext (.node S (.leaf x)) V

theorem leaf_context_of_off {S V : Tree} {h : RMAF.Vertex}
 (hn : (leaves S).Nodup) (hh : subtree S h=some V)
 (off : ∀ q W,subtree S q=some W → (∀x,x∈leaves W → x∉leaves V) → ∃c,W=.leaf c) :
 LeafContext S V := by
 induction S generalizing h with
 | leaf x =>
   cases h with
   | nil => have eq : Tree.leaf x=V := Option.some.inj hh; subst V; exact .here _
   | cons s h => simp [subtree] at hh
 | node l r il ir =>
   cases h with
   | nil => have eq : Tree.node l r=V := Option.some.inj hh; subst V; exact .here _
   | cons s h =>
     obtain ⟨nl,nr,dj⟩ := List.nodup_append.1 hn
     cases s
     · have subV : leaves V ⊆ leaves l := by rw [←source_subtree_labels hh]; exact (subtreeLabels_sublist l h).subset
       obtain ⟨c,eq⟩ := off [true] r rfl (by intro x xr xv; exact dj x (subV xv) x xr rfl)
       have smaller := il nl hh (by intro q W hq all; exact off (false::q) W hq all)
       subst r; exact .right c smaller
     · have subV : leaves V ⊆ leaves r := by rw [←source_subtree_labels hh]; exact (subtreeLabels_sublist r h).subset
       obtain ⟨c,eq⟩ := off [false] l rfl (by intro x xl xv; exact dj x xl x (subV xv) rfl)
       have smaller := ir nr hh (by intro q W hq all; exact off (true::q) W hq all)
       subst l; exact .left c smaller

theorem remaining_full_source_geometry {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b=some .remaining) :
 ∃ h p s t r U x y f c, ((x=a ∧ y=b) ∨ (x=b ∧ y=a)) ∧
 subtree S p=some (fork s (.leaf x) U) ∧
 (cuts S a b=[p++[!s],f] ∨ cuts S a b=[f,p++[!s]]) ∧ subtree S f=some (.leaf c) ∧
 restrictionAgrees T S (subtreeLabels S (p++[!s]))=false ∧
 restrictionAgrees T S (coreLabels S a b)=true ∧
 subtree S h=some (fork r (fork t (fork s (.leaf x) U) (.leaf c)) (.leaf y)) ∧
 LeafContext S (fork r (fork t (fork s (.leaf x) U) (.leaf c)) (.leaf y)) := by
 obtain ⟨h,p,s,t,r,U,x,y,f,c,xy,hp,cut,hf,bad,gc,hh⟩ := remaining_source_spine ch sel
 have facts := selectLocal_cases sel
 have hn := (properPair_parts (admitted_parts facts.1).1).2.1
 let V := fork r (fork t (fork s (.leaf x) U) (.leaf c)) (.leaf y)
 have Usub : leaves U ⊆ leaves V := by
   intro z hz
   exact (fork_mem r _ _ _).2 (Or.inl ((fork_mem t _ _ _).2 (Or.inl ((fork_mem s _ _ _).2 (Or.inr hz)))))
 have cV : c∈leaves V := (fork_mem r _ _ _).2 (Or.inl ((fork_mem t _ _ _).2 (Or.inr (by simp [leaves]))))
 have xV : x∈leaves V := (fork_mem r _ _ _).2 (Or.inl ((fork_mem t _ _ _).2 (Or.inl ((fork_mem s _ _ _).2 (Or.inl (by simp [leaves]))))))
 have yV : y∈leaves V := (fork_mem r _ _ _).2 (Or.inr (by simp [leaves]))
 have aV : a∈leaves V := by rcases xy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
 have bV : b∈leaves V := by rcases xy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
 have htU : subtree S (p++[!s])=some U := by rw [subtree_append hp]; exact fork_second s _ _
 have ctx : LeafContext S V := by
   apply leaf_context_of_off hn hh
   intro q W hq outside
   have all : ∀z,z∈leaves W → z∈coreLabels S a b := by
     intro z hz
     have zS := (subtreeLabels_sublist S q).subset (by rw [source_subtree_labels hq]; exact hz)
     have nu : z∉subtreeLabels S (p++[!s]) := by
       rw [source_subtree_labels htU]
       exact fun zu => outside z hz (Usub zu)
     have nc : z≠c := by intro eq; subst z; exact outside c hz cV
     exact core_of_neither_pendant cut hf zS nu nc
   exact outside_subtree_leaf facts.2.2.2 gc hq all
     (fun aw => outside a aw aV) (fun bw => outside b bw bV)
 exact ⟨h,p,s,t,r,U,x,y,f,c,xy,hp,cut,hf,bad,gc,hh,ctx⟩

end Universal233.Rule5FinalClassification
