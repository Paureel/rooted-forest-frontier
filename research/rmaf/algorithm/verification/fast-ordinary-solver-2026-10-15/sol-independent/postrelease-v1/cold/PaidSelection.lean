import PaidPartitions
namespace Universal233.Case322PaidGuard
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction
set_option maxRecDepth 20000

theorem cherry_a_bc_pendant {T : Tree} {qa ub uc : RMAF.Vertex} {a b c : Nat}
 (hn : (leaves T).Nodup) (ch : ActualCherry T a b)
 (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
 qa ∈ cuts T b c ∧ b ∈ subtreeLabels T qa.dropLast := by
 obtain ⟨p,ch | ch⟩ := ch
 all_goals
   have one : ∀ {sideA sideB : Bool}, LeafAt T (p++[sideA]) a →
       LeafAt T (p++[sideB]) b → qa ∈ cuts T b c ∧ b ∈ subtreeLabels T qa.dropLast := by
     intro sideA sideB lA lB
     have ae := leaf_unique hn la lA
     have bspan := (minimalVertices_terminal [b,c] T (p++[sideB]) b lB).2 (by simp)
     have cspan := (minimalVertices_terminal [b,c] T uc c lc).2 (by simp)
     have neq : uc ≠ p++[sideB] := by
       intro e; rw [e] at lc
       exact hbc (Tree.leaf.inj (Option.some.inj (lB.symm.trans lc)))
     have occ := walk_from_leaf_visits_parent lB (minimalVertices_connected [b,c] T _ _ bspan cspan) neq
     have pe : qa.dropLast = p := by simp [ae]
     have off : qa ∉ minimalVertices [b,c] T := by
       intro h
       have h := (minimalVertices_terminal [b,c] T qa a la).1 h
       simpa [hab,hac] using h
     refine ⟨(cuts_spec T b c qa).2 ⟨la.valid,?_,by simpa [pe] using occ,off⟩,?_⟩
     · rw [ae]; simp
     · rw [pe]
       exact (subtreeLabels_prefix T p b).2 ⟨p++[sideB],lB,List.prefix_append _ _⟩
 · exact one (cherry_left ch) (cherry_right ch)
 · exact one (cherry_right ch) (cherry_left ch)

theorem cside_branch_currentGuard {T S : Tree} {qa ub uc q : RMAF.Vertex} {a b c : Nat}
 (hn : (leaves T).Nodup) (ch : ActualCherry T a b)
 (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hq : q ∈ cSideEdges T b c) :
 currentGuard T S (targetBranch T [qa,q]) = true := by
 have aedge := cherry_a_bc_pendant hn ch la lb lc hab hac hbc
 have qedge := cSideEdges_sound hq
 have ne : qa ≠ q := by
   intro e; exact qedge.2.2 (e ▸ aedge.2)
 apply pendant_subset_currentGuard (a:=b) (b:=c) hn (leafAt_label T ub b lb) [qa,q]
 · simp [ne]
 · intro r hr
   rcases (by simpa using hr : r = qa ∨ r = q) with rfl | rfl
   · exact aedge.1
   · exact qedge.1

theorem bside_branch_currentGuard {T S : Tree} {qa ub uc : RMAF.Vertex} {a b c : Nat}
 (hn : (leaves T).Nodup) (ch : ActualCherry T a b)
 (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
 currentGuard T S (targetBranch T (qa::bSideWithoutA T a b c)) = true := by
 have aedge := (cherry_a_bc_pendant hn ch la lb lc hab hac hbc).1
 have nd : (bSideWithoutA T a b c).Nodup :=
   ((pendantOriginal_nodup T b c).filter _).filter _
 have noA : qa ∉ bSideWithoutA T a b c := by
   intro h
   have hh := (List.mem_filter.1 h).2
   rw [source_subtree_labels la] at hh
   simp [leaves] at hh
 apply pendant_subset_currentGuard (a:=b) (b:=c) hn (leafAt_label T ub b lb)
   (qa::bSideWithoutA T a b c) (List.nodup_cons.2 ⟨noA,nd⟩)
 intro q hq
 rcases List.mem_cons.1 hq with rfl | hq
 · exact aedge
 · exact (bSideEdges_sound (List.mem_filter.1 hq).1).1

end Universal233.Case322PaidGuard
