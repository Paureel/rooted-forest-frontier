import PaidAncestor
namespace Universal233.Case322PaidGuard
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction
set_option maxRecDepth 20000

theorem common_prefix_lca {p u v : RMAF.Vertex} (pu : p <+: u) (pv : p <+: v) : p <+: lca u v := by
 induction p generalizing u v with
 | nil => exact List.nil_prefix
 | cons s p ih =>
   obtain ⟨ut,rfl⟩ := pu
   obtain ⟨vt,rfl⟩ := pv
   obtain ⟨tail,h⟩ := ih (List.prefix_append _ _) (List.prefix_append _ _)
   exact ⟨tail,by simpa [lca] using congrArg (s::·) h⟩

theorem prefix_root_path {p u : RMAF.Vertex} (hp : p <+: u) : PathAt p [] u := by
 obtain ⟨tail,rfl⟩ := hp
 induction p with
 | nil => exact .endpointL [] tail
 | cons s p ih => exact .rightLeg s ih

theorem path_prefix_one {p u v : RMAF.Vertex} (h : PathAt p u v) : p <+: u ∨ p <+: v := by
 induction h with
 | endpointL => exact Or.inl List.prefix_rfl
 | endpointR => exact Or.inr List.prefix_rfl
 | fork => exact Or.inl List.nil_prefix
 | fork' => exact Or.inl List.nil_prefix
 | down s h ih =>
   rcases ih with ⟨t,e⟩ | ⟨t,e⟩
   · exact Or.inl ⟨t,by simpa using congrArg (s::·) e⟩
   · exact Or.inr ⟨t,by simpa using congrArg (s::·) e⟩
 | leftLeg s h ih =>
   obtain ⟨t,e⟩ := path_root_prefix h
   exact Or.inl ⟨t,by simpa using congrArg (s::·) e⟩
 | rightLeg s h ih =>
   obtain ⟨t,e⟩ := path_root_prefix (path_sym h)
   exact Or.inr ⟨t,by simpa using congrArg (s::·) e⟩
 | crossLeft s h ih =>
   obtain ⟨t,e⟩ := path_root_prefix h
   exact Or.inl ⟨t,by simpa using congrArg (s::·) e⟩
 | crossRight s h ih =>
   obtain ⟨t,e⟩ := path_root_prefix (path_sym h)
   exact Or.inr ⟨t,by simpa using congrArg (s::·) e⟩

theorem sibling_no_common_descendant (p : RMAF.Vertex) (s : Bool) {u : RMAF.Vertex}
 (one : p++[s] <+: u) : ¬p++[!s] <+: u := by
 intro other
 have len : (p++[s]).length = (p++[!s]).length := by simp
 have ne : p++[s] ≠ p++[!s] := by cases s <;> simp
 rcases List.prefix_or_prefix_of_prefix one other with h | h
 · exact ne (h.eq_of_length len)
 · exact ne (h.eq_of_length len.symm).symm

/-- An outgoing hull boundary into a non-X subtree cannot have the original
root as its tail: all X labels would then lie in the other root child. -/
theorem outgoing_tail_nonroot {T : Tree} {X : List Nat} {r : RMAF.Vertex}
 (hn : (leaves T).Nodup) (valid : Valid T r) (nr : r ≠ [])
 (subset : ∀ x, x ∈ X → x ∈ leaves T)
 (disj : ∀ x, x ∈ X → x ∉ subtreeLabels T r)
 (tailHull : r.dropLast ∈ minimalVertices X T) : r.dropLast ≠ [] := by
 intro e
 rcases List.eq_nil_or_concat r with nil | ⟨p,s,eq⟩
 · exact nr nil
 have re : r = p++[s] := by simpa only [List.concat_eq_append] using eq
 have pe : p = [] := by simpa [re] using e
 subst p
 simp only [List.nil_append] at re
 cases T with
 | leaf x => obtain ⟨U,hU⟩ := valid; simp [re,subtree] at hU
 | node L R =>
   have mono : ∀ x, x ∈ X → x ∈ subtreeLabels (.node L R) [!s] := by
     intro x hx
     have all := subset x hx
     have no := disj x hx
     cases s
     · simp [re,subtreeLabels,leaves] at all no ⊢
       exact all.resolve_left no
     · simp [re,subtreeLabels,leaves] at all no ⊢
       exact all.resolve_right no
   have hull := BinaryExchange.hull_mono (.node L R) X (subtreeLabels (.node L R) [!s]) mono []
     ((minimalVertices_correct X (.node L R) []).1 (by simpa [e] using tailHull))
   have pref := subtree_hull hn [!s] []
     ((minimalVertices_correct _ (.node L R) []).2 hull)
   have len := pref.length_le
   simp at len

/-- At a root b--c LCA, an outgoing X-hull frontier into the actual core
forces a literal b-side pendant other than a. The proof constructs its sibling
original edge; it does not use a budget or guard premise. -/
theorem outgoing_core_root_forces_bside {T : Tree} {X : List Nat}
 {r qa ub uc : RMAF.Vertex} {a b c : Nat}
 (hn : (leaves T).Nodup) (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (valid : Valid T r) (nr : r ≠ [])
 (ar : a ∈ subtreeLabels T r) (br : b ∈ subtreeLabels T r)
 (subset : ∀ x, x ∈ X → x ∈ leaves T)
 (disj : ∀ x, x ∈ X → x ∉ subtreeLabels T r)
 (tailHull : r.dropLast ∈ minimalVertices X T)
 (root : lca ub uc = []) : bSideWithoutA T a b c ≠ [] := by
 have pnr := outgoing_tail_nonroot hn valid nr subset disj tailHull
 rcases List.eq_nil_or_concat r with nil | ⟨p,s,eq⟩
 · exact False.elim (nr nil)
 have re : r = p++[s] := by simpa only [List.concat_eq_append] using eq
 have pe : r.dropLast = p := by simp [re]
 have pne : p ≠ [] := by simpa [pe] using pnr
 have rB := (label_in_subtree_iff_prefix hn lb).1 br
 have rA := (label_in_subtree_iff_prefix hn la).1 ar
 have pB : p <+: ub := (by rw [re]; exact List.prefix_append _ _ : p <+: r).trans rB
 have pNotC : ¬p <+: uc := by
   intro pC
   have pre := common_prefix_lca pB pC
   rw [root] at pre
   have len := pre.length_le
   cases p with
   | nil => exact pne rfl
   | cons t p => simp at len
 let q := p++[!s]
 have qvalid : Valid T q := by
   obtain ⟨P,hP⟩ := valid_ancestor valid (by rw [re]; exact List.prefix_append _ _ : p <+: r)
   obtain ⟨U,hU⟩ := valid
   rw [re,subtree_append hP] at hU
   cases P with
   | leaf x => simp [subtree] at hU
   | node L R =>
     refine ⟨if s then L else R,?_⟩
     dsimp [q]
     rw [subtree_append hP]
     cases s <;> rfl
 have qDrop : q.dropLast = p := by simp [q]
 have qNotB : ¬q <+: ub := by
   apply sibling_no_common_descendant p s
   simpa [re] using rB
 have qNotA : ¬q <+: qa := by
   apply sibling_no_common_descendant p s
   simpa [re] using rA
 have qNotC : ¬q <+: uc := by
   intro h; exact pNotC ((List.prefix_append _ _).trans h)
 obtain ⟨W,lookup,bW,cW,top⟩ := actual_lca_geometry hn lb lc
 have rootHull : [] ∈ minimalVertices [b,c] T := by simpa [root] using top
 have bHull := (minimalVertices_terminal [b,c] T ub b lb).2 (by simp)
 have pHull : p ∈ minimalVertices [b,c] T :=
   minimal_convex [b,c] T p [] ub rootHull bHull (prefix_root_path pB)
 have qOff : q ∉ minimalVertices [b,c] T := by
   intro h
   rcases path_prefix_one ((pair_minimal_path hn lb lc q).1 h) with h | h
   · exact qNotB h
   · exact qNotC h
 have qCut : q ∈ cuts T b c := (cuts_spec T b c q).2
   ⟨qvalid,by simp [q],by simpa [qDrop] using pHull,qOff⟩
 have bP : b ∈ subtreeLabels T q.dropLast := by
   rw [qDrop]; exact (label_in_subtree_iff_prefix hn lb).2 pB
 have cP : c ∉ subtreeLabels T q.dropLast := by
   rw [qDrop]; exact fun h => pNotC ((label_in_subtree_iff_prefix hn lc).1 h)
 have aQ : a ∉ subtreeLabels T q := fun h => qNotA ((label_in_subtree_iff_prefix hn la).1 h)
 have mem : q ∈ bSideWithoutA T a b c := by
   apply List.mem_filter.2
   refine ⟨List.mem_filter.2 ⟨qCut,?_⟩,?_⟩
   · simp [bP,cP]
   · simp [aQ]
 intro empty
 rw [empty] at mem
 exact List.not_mem_nil mem

theorem fallback_lca_nonroot {T : Tree} {X : List Nat}
 {r qa ub uc : RMAF.Vertex} {a b c : Nat}
 (hn : (leaves T).Nodup) (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (valid : Valid T r) (nr : r ≠ [])
 (ar : a ∈ subtreeLabels T r) (br : b ∈ subtreeLabels T r)
 (subset : ∀ x, x ∈ X → x ∈ leaves T)
 (disj : ∀ x, x ∈ X → x ∉ subtreeLabels T r)
 (tailHull : r.dropLast ∈ minimalVertices X T)
 (empty : bSideWithoutA T a b c = []) : lca ub uc ≠ [] := by
 intro root
 exact outgoing_core_root_forces_bside hn la lb lc valid nr ar br subset disj tailHull root empty

end Universal233.Case322PaidGuard
