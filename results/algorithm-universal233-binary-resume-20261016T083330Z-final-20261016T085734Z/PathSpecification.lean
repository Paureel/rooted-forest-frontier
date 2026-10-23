import PlanCosts
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322

theorem label_in_subtree_iff_prefix {T : Tree} {u p : RMAF.Vertex} {x : Nat}
 (hn : (leaves T).Nodup) (leaf : LeafAt T u x) : x ∈ subtreeLabels T p ↔ p <+: u := by
 constructor
 · intro h
   obtain ⟨v,lv,pv⟩ := (subtreeLabels_prefix T p x).1 h
   exact (leaf_unique hn lv leaf) ▸ pv
 · exact fun hp => (subtreeLabels_prefix T p x).2 ⟨u,leaf,hp⟩

/-- Literal original path-side pendant criterion. The parent lies on the
b--c path, is below their LCA on the endpoint side, and is not the endpoint
leaf because it has the original child q. -/
def InteriorPendant (T : Tree) (u v q : RMAF.Vertex) : Prop :=
 ∃ p s, q = p ++ [s] ∧ Adj T p q ∧ PathAt p u v ∧ ¬PathAt q u v ∧ p <+: u ∧ ¬p <+: v

theorem bside_literal_spec {T : Tree} {ub uc q : RMAF.Vertex} {b c : Nat}
 (hn : (leaves T).Nodup) (lb : LeafAt T ub b) (lc : LeafAt T uc c) :
 q ∈ bSideEdges T b c ↔ InteriorPendant T ub uc q := by
 constructor
 · intro h
   have hs := bSideEdges_sound h
   obtain ⟨p,s,eq,adj,on,off⟩ := (original_pendant_spec hn lb lc q).1 hs.1
   have pEq : q.dropLast = p := by simp [eq]
   refine ⟨p,s,eq,adj,on,off,?_,?_⟩
   · apply (label_in_subtree_iff_prefix hn lb).1
     simpa [pEq] using hs.2.1
   · intro pref
     exact hs.2.2 (by simpa [pEq] using (label_in_subtree_iff_prefix hn lc).2 pref)
 · rintro ⟨p,s,eq,adj,on,off,bpref,cnpref⟩
   have cut := (original_pendant_spec hn lb lc q).2 ⟨p,s,eq,adj,on,off⟩
   have pEq : q.dropLast = p := by simp [eq]
   have bb : b ∈ subtreeLabels T q.dropLast := by simpa [pEq] using (label_in_subtree_iff_prefix hn lb).2 bpref
   have cc : c ∉ subtreeLabels T q.dropLast := by
     intro h; exact cnpref ((label_in_subtree_iff_prefix hn lc).1 (by simpa [pEq] using h))
   exact List.mem_filter.2 ⟨cut,by simp [bb,cc]⟩

theorem cside_literal_spec {T : Tree} {ub uc q : RMAF.Vertex} {b c : Nat}
 (hn : (leaves T).Nodup) (lb : LeafAt T ub b) (lc : LeafAt T uc c) :
 q ∈ cSideEdges T b c ↔ InteriorPendant T uc ub q := by
 have same : cSideEdges T b c = bSideEdges T c b := by unfold cSideEdges bSideEdges; rw [cuts_swap T b c]
 rw [same]
 exact bside_literal_spec hn lc lb

/-- Under the actual original cherry, the only b--c pendant containing a is
the original terminal a arc. This proves the literal 'excluding the arc to a'
filter, rather than assuming that selected descendants are all in X. -/
theorem cherry_pendant_containing_a {T : Tree} {qa uc q : RMAF.Vertex} {a b c : Nat}
 (hn : (leaves T).Nodup) (ch : ActualCherry T a b)
 (la : LeafAt T qa a) (lc : LeafAt T uc c) (hbc : b ≠ c)
 (hq : q ∈ cuts T b c) : a ∈ subtreeLabels T q ↔ q = qa := by
 constructor
 · intro aQ
   have qA := (label_in_subtree_iff_prefix hn la).1 aQ
   have spec := (cuts_spec T b c q).1 hq
   obtain ⟨p,ch | ch⟩ := ch
   all_goals
     have one : ∀ {sideA sideB : Bool}, LeafAt T (p++[sideA]) a → LeafAt T (p++[sideB]) b → q = qa := by
       intro sideA sideB lA lB
       have ae := leaf_unique hn la lA
       have bspan := (minimalVertices_terminal [b,c] T (p++[sideB]) b lB).2 (by simp)
       have cspan := (minimalVertices_terminal [b,c] T uc c lc).2 (by simp)
       have ne : uc ≠ p++[sideB] := by
         intro e
         rw [e] at lc
         unfold LeafAt at lc lB
         exact hbc (Tree.leaf.inj (Option.some.inj (lB.symm.trans lc)))
       have occ := walk_from_leaf_visits_parent lB (minimalVertices_connected [b,c] T _ _ bspan cspan) ne
       have noQp := offpath_no_descendant spec.2.1 spec.2.2.1 spec.2.2.2 occ
       by_cases eq : q = qa
       · exact eq
       · have qlen : q.length < qa.length := by
           have le := qA.length_le
           have nq : q.length ≠ qa.length := fun e => eq (qA.eq_of_length e)
           omega
         have qaLen : qa.length = p.length+1 := by simp [ae]
         have pp : p <+: qa := by rw [ae]; exact List.prefix_append _ _
         exact False.elim (noQp (List.prefix_of_prefix_length_le qA pp (by omega)))
   · exact one (cherry_left ch) (cherry_right ch)
   · exact one (cherry_right ch) (cherry_left ch)
 · intro e; subst q; rw [source_subtree_labels la]; simp [leaves]

theorem bside_without_a_literal_spec {T : Tree} {qa ub uc q : RMAF.Vertex} {a b c : Nat}
 (hn : (leaves T).Nodup) (ch : ActualCherry T a b)
 (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c) (hbc : b ≠ c) :
 q ∈ bSideWithoutA T a b c ↔ InteriorPendant T ub uc q ∧ q ≠ qa := by
 constructor
 · intro h
   have hh := List.mem_filter.1 h
   refine ⟨(bside_literal_spec hn lb lc).1 hh.1,?_⟩
   intro e
   have aQ := (cherry_pendant_containing_a hn ch la lc hbc (bSideEdges_sound hh.1).1).2 e
   simp [aQ] at hh
 · rintro ⟨path,ne⟩
   have edge := (bside_literal_spec hn lb lc).2 path
   have noA : a ∉ subtreeLabels T q := by
     intro aQ; exact ne ((cherry_pendant_containing_a hn ch la lc hbc (bSideEdges_sound edge).1).1 aQ)
   exact List.mem_filter.2 ⟨edge,by simp [noA]⟩
end Universal233.Case322Extraction
