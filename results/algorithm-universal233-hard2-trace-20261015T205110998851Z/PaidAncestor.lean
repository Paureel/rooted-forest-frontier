import PaidSelection
namespace Universal233.Case322PaidGuard
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction
set_option maxRecDepth 20000

theorem nonroot_cluster_outside {T : Tree} {q : RMAF.Vertex}
 (hn : (leaves T).Nodup) (valid : Valid T q) (nr : q ≠ []) :
 ∃ z, z ∈ leaves T ∧ z ∉ subtreeLabels T q := by
 cases q with
 | nil => exact False.elim (nr rfl)
 | cons side q =>
   cases T with
   | leaf x => obtain ⟨U,hU⟩ := valid; simp [subtree] at hU
   | node L R =>
     have nd := List.nodup_append.1 hn
     cases side
     · obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _ (tree_leaves_nonempty R)
       refine ⟨z,List.mem_append_right _ hz,?_⟩
       intro hin
       exact nd.2.2 z ((subtreeLabels_sublist L q).subset hin) z hz rfl
     · obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _ (tree_leaves_nonempty L)
       refine ⟨z,List.mem_append_left _ hz,?_⟩
       intro hin
       exact nd.2.2 z hz z ((subtreeLabels_sublist R q).subset hin) rfl

theorem cherry_ancestor_contains_a {T : Tree} {q qa ub uc : RMAF.Vertex} {a b c : Nat}
 (hn : (leaves T).Nodup) (ch : ActualCherry T a b)
 (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (hbc : b ≠ c) (bq : b ∈ subtreeLabels T q) (cq : c ∈ subtreeLabels T q) :
 a ∈ subtreeLabels T q := by
 have qb := (label_in_subtree_iff_prefix hn lb).1 bq
 have qc := (label_in_subtree_iff_prefix hn lc).1 cq
 have ne : q ≠ ub := by
   intro e
   have ce := leaf_valid_descendant lb lc.valid (by simpa [e] using qc)
   rw [ce] at lc
   exact hbc (Tree.leaf.inj (Option.some.inj (lb.symm.trans lc)))
 obtain ⟨p,ch | ch⟩ := ch
 all_goals
   have one : ∀ {sa sb : Bool}, LeafAt T (p++[sa]) a → LeafAt T (p++[sb]) b → a ∈ subtreeLabels T q := by
     intro sa sb lA lB
     have ae := leaf_unique hn la lA
     have be := leaf_unique hn lb lB
     have len : q.length ≤ p.length := by
       have le := qb.length_le
       have neq : q.length ≠ ub.length := fun h => ne (qb.eq_of_length h)
       have blen : ub.length = p.length+1 := by simp [be]
       omega
     have qp : q <+: p := List.prefix_of_prefix_length_le qb (by rw [be]; exact List.prefix_append _ _) len
     apply (label_in_subtree_iff_prefix hn la).2
     rw [ae]
     exact qp.trans (List.prefix_append _ _)
 · exact one (cherry_left ch) (cherry_right ch)
 · exact one (cherry_right ch) (cherry_left ch)

theorem split_single_mixed_length {L X : List Nat}
 (yes : ∃ x, x ∈ L ∧ x ∈ X) (no : ∃ x, x ∈ L ∧ x ∉ X) :
 (splitForest [L] X).length = 2 := by
 obtain ⟨x,xL,xX⟩ := yes
 obtain ⟨y,yL,yX⟩ := no
 have ey : BinaryExchange.yes L X.contains ≠ [] := by
   have hx : x ∈ BinaryExchange.yes L X.contains := by simp [BinaryExchange.yes,xL,xX]
   intro e; rw [e] at hx; exact List.not_mem_nil hx
 have en : BinaryExchange.no L X.contains ≠ [] := by
   have hy : y ∈ BinaryExchange.no L X.contains := by simp [BinaryExchange.no,yL,yX]
   intro e; rw [e] at hy; exact List.not_mem_nil hy
 simp [splitForest,BinaryExchange.splitAll,BinaryExchange.split,
   (BinaryExchange.isEmpty_false _).2 ey,(BinaryExchange.isEmpty_false _).2 en]

theorem ancestor_branch_currentGuard {T S : Tree} {q qa ub uc : RMAF.Vertex} {a b c : Nat}
 (hn : (leaves T).Nodup) (ch : ActualCherry T a b)
 (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (hab : a ≠ b) (hbc : b ≠ c)
 (valid : Valid T q) (nr : q ≠ [])
 (bq : b ∈ subtreeLabels T q) (cq : c ∈ subtreeLabels T q) :
 currentGuard T S (targetBranch T [qa,q]) = true := by
 have aq := cherry_ancestor_contains_a hn ch la lb lc hbc bq cq
 obtain ⟨z,zT,zq⟩ := nonroot_cluster_outside hn valid nr
 have za : z ≠ a := by intro e; subst z; exact zq aq
 have qaNr := terminal_nonroot la (leafAt_label T ub b lb) hab
 have ne : qa ≠ q := by
   intro e; rw [←e,source_subtree_labels la] at bq
   exact hab (show b = a from by simpa [leaves] using bq).symm
 have bind := singleton_partition_binding hn la (leafAt_label T ub b lb) hab
 have aSplit : splitForest [[a]] (subtreeLabels T q) = [[a]] := by
   simp [splitForest,BinaryExchange.splitAll,BinaryExchange.split,BinaryExchange.yes,BinaryExchange.no,aq]
 let R := (leaves T).filter (fun x => x != a)
 have bR : b ∈ R := by simp [R,leafAt_label T ub b lb,Ne.symm hab]
 have zR : z ∈ R := by simp [R,zT,za]
 have len := split_single_mixed_length (X:=subtreeLabels T q) ⟨b,bR,bq⟩ ⟨z,zR,zq⟩
 have components : (arcPartition T [qa,q]).length = 3 := by
   have h : arcPartition T [qa,q] = splitForest (arcPartition T [qa]) (subtreeLabels T q) := rfl
   rw [h,bind]
   change (splitForest ([[a]]++[R]) (subtreeLabels T q)).length = 3
   rw [splitForest_append,aSplit,List.length_append,len]
   rfl
 apply target_currentGuard_of_nonredundant hn [qa,q] (by simp [ne])
 · intro p hp; rcases (by simpa using hp : p = qa ∨ p = q) with rfl | rfl
   · exact la.valid
   · exact valid
 · intro p hp; rcases (by simpa using hp : p = qa ∨ p = q) with rfl | rfl
   · exact qaNr
   · exact nr
 · exact components

end Universal233.Case322PaidGuard
