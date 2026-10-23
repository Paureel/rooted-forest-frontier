import OrientedPathCover
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322
set_option maxRecDepth 15000

theorem lca_prefixes (p q : RMAF.Vertex) : lca p q <+: p ∧ lca p q <+: q := by
 induction p generalizing q with
 | nil => exact ⟨List.nil_prefix,List.nil_prefix⟩
 | cons s p ih =>
   cases q with
   | nil => exact ⟨List.nil_prefix,List.nil_prefix⟩
   | cons t q =>
     by_cases e : s = t
     · subst t
       obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := ih q
       refine ⟨⟨u,?_⟩,⟨v,?_⟩⟩
       · simpa [lca] using congrArg (s::·) hu
       · simpa [lca] using congrArg (s::·) hv
     · simp [lca,e]

theorem actual_lca_geometry {T : Tree} {ub uc : RMAF.Vertex} {b c : Nat}
 (hn : (leaves T).Nodup) (lb : LeafAt T ub b) (lc : LeafAt T uc c) :
 ∃ W, subtree T (lca ub uc) = some W ∧ b ∈ leaves W ∧ c ∈ leaves W ∧
 lca ub uc ∈ minimalVertices [b,c] T := by
 have pp := lca_prefixes ub uc
 obtain ⟨W,lookup⟩ := valid_ancestor lb.valid pp.1
 have bL : b ∈ subtreeLabels T (lca ub uc) := (subtreeLabels_prefix T _ b).2 ⟨ub,lb,pp.1⟩
 have cL : c ∈ subtreeLabels T (lca ub uc) := (subtreeLabels_prefix T _ c).2 ⟨uc,lc,pp.2⟩
 rw [source_subtree_labels lookup] at bL cL
 exact ⟨W,lookup,bL,cL,(pair_minimal_path hn lb lc _).2 (lca_on_path ub uc)⟩

theorem oriented_typeIII_cover {T S X C : Tree} {w r qa ub uc : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (ch : ActualCherry T a b) (two : (cuts S a b).length = 2)
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (leafA : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (ha : agreement T S F = true) :
 ∃ P, P ∈ typeIIChildren T S a b qa [lca ub uc] ∧ OriginalCover T S F P := by
 rcases oriented_hard2_or_b_or_bcx hnT hnS same he ch two ha with hard | singleB | ⟨singleA,B,hB,bB,cB,_⟩
 · exact ⟨pendantPartition S a b,by simp [typeIIChildren],hard⟩
 · exact ⟨singletonPartition S b,by simp [typeIIChildren],F,ha,Nat.le_refl _,singleton_refinement ha singleB⟩
 · obtain ⟨W,lookup,bW,cW,onPath⟩ := actual_lca_geometry hnT lb lc
   refine ⟨arcPartition T [qa,lca ub uc],by simp [typeIIChildren],F,ha,Nat.le_refl _,?_⟩
   apply singleton_plus_unused_refines [lca ub uc] ha leafA singleA
   intro q hq
   have eq : q = lca ub uc := by simpa using hq
   subst q
   rw [source_subtree_labels lookup]
   exact oriented_ancestor_unused hnT hnS he core coreLabels bC cC lookup bW cW onPath ha singleA hB bB cB
     (unordered_cherry_distinct hnT ch)

/-- Literal original path selection. Every selected original b-side arc is
kept and paid; the fallback keeps the actual LCA address, including an invalid
root address until the separate current guard is proved. -/
def rawPlan (T S : Tree) (a b c : Nat) (qa qb ub uc : RMAF.Vertex) : List Branch :=
 match cSideEdges T b c with
 | q::r::_ => typeIBranches T S a b qa qb q r
 | _ => match bSideWithoutA T a b c with
   | [] => typeIIBranches T S a b qa qb [lca ub uc]
   | qs => typeIIBranches T S a b qa qb qs

theorem rawPlan_original_cover {T S X C : Tree} {w r qa qb ub uc : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (ch : ActualCherry T a b) (two : (cuts S a b).length = 2)
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (leafA : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (ha : agreement T S F = true) :
 ∃ child, child ∈ rawPlan T S a b c qa qb ub uc ∧ OriginalCover T S F child.partition := by
 have convert : ∀ (cs : List Branch), (∃ P, P ∈ cs.map Branch.partition ∧ OriginalCover T S F P) →
   ∃ child, child ∈ cs ∧ OriginalCover T S F child.partition := fun cs h => partition_cover_to_branch_cover h
 cases eq : cSideEdges T b c with
 | nil =>
   cases eb : bSideWithoutA T a b c with
   | nil =>
     have h := oriented_typeIII_cover hnT hnS same he ch two core coreLabels bC cC leafA lb lc ha
     have h' : ∃ P, P ∈ (typeIIBranches T S a b qa qb [lca ub uc]).map Branch.partition ∧ OriginalCover T S F P := h
     simpa [rawPlan,eq,eb] using convert _ h'
   | cons q qs =>
     have h := oriented_computed_typeII_cover hnT hnS same he ch two core coreLabels bC cC leafA ha
     have h' : ∃ P, P ∈ (typeIIBranches T S a b qa qb (bSideWithoutA T a b c)).map Branch.partition ∧ OriginalCover T S F P := h
     simpa [rawPlan,eq,eb] using convert _ h'
 | cons q qs =>
   cases qs with
   | nil =>
     cases eb : bSideWithoutA T a b c with
     | nil =>
       have h := oriented_typeIII_cover hnT hnS same he ch two core coreLabels bC cC leafA lb lc ha
       have h' : ∃ P, P ∈ (typeIIBranches T S a b qa qb [lca ub uc]).map Branch.partition ∧ OriginalCover T S F P := h
       simpa [rawPlan,eq,eb] using convert _ h'
     | cons z zs =>
       have h := oriented_computed_typeII_cover hnT hnS same he ch two core coreLabels bC cC leafA ha
       have h' : ∃ P, P ∈ (typeIIBranches T S a b qa qb (bSideWithoutA T a b c)).map Branch.partition ∧ OriginalCover T S F P := h
       simpa [rawPlan,eq,eb] using convert _ h'
   | cons t ts =>
     have qmem : q ∈ cSideEdges T b c := by simp [eq]
     have tmem : t ∈ cSideEdges T b c := by simp [eq]
     have nd : (cSideEdges T b c).Nodup := (pendantOriginal_nodup T b c).filter _
     have ne : q ≠ t := by
       rw [eq] at nd
       exact fun e => (List.nodup_cons.1 nd).1 (by simp [e])
     have h := oriented_computed_typeI_cover hnT hnS same he ch two core coreLabels bC cC leafA qmem tmem ne ha
     have h' : ∃ P, P ∈ (typeIBranches T S a b qa qb q t).map Branch.partition ∧ OriginalCover T S F P := h
     simpa [rawPlan,eq] using convert _ h'
end Universal233.Case322Extraction
