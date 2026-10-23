import Case322Partition
namespace Universal233.Rule5Case322
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local
set_option maxRecDepth 10000

def OriginalCover (T S : Tree) (F : List (List Nat)) (P : List (List Nat)) : Prop :=
 ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧ Refines G P

/-- The full ordinary local alternative before choosing a path family. The
hard2 branch returns a no-larger original AF; its saving is derived above. -/
theorem hard2_or_b_or_bcx {T S X : Tree} {w : RMAF.Vertex}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (ch : ActualCherry T a b)
 (hc : cuts S a b = [w ++ [false,false,true],w ++ [false,true]])
 (ha : agreement T S F = true) :
 OriginalCover T S F (pendantPartition S a b) ∨ [b] ∈ F ∨
 ([a] ∈ F ∧ ∃ B, B ∈ F ∧ b ∈ B ∧ c ∈ B ∧ ∃ x, x ∈ B ∧ x ∈ leaves X) := by
 rcases actual_unordered_pendant_safety hnS ha ch with singleA | singleB | ref
 · by_cases singleB : [b] ∈ F
   · exact Or.inr (Or.inl singleB)
   · by_cases noBCX : ∀ D, D ∈ F → b ∈ D → c ∈ D → ∀ x, x ∈ D → x ∈ leaves X → False
     · exact Or.inl (actual_easy_exchange_unordered hnT hnS same he ch hc ha singleA singleB noBCX)
     · right; right
       refine ⟨singleA,?_⟩
       apply Classical.byContradiction
       intro no
       apply noBCX
       intro D hD bD cD x xD xX
       exact no ⟨D,hD,bD,cD,x,xD,xX⟩
 · exact Or.inr (Or.inl singleB)
 · exact Or.inl ⟨F,ha,Nat.le_refl _,ref⟩

def typeIChildren (T S : Tree) (a b : Nat) (qa q r : RMAF.Vertex) :=
 [pendantPartition S a b,singletonPartition S b,arcPartition T [qa,q],arcPartition T [qa,r]]
def typeIIChildren (T S : Tree) (a b : Nat) (qa : RMAF.Vertex) (qs : List RMAF.Vertex) :=
 [pendantPartition S a b,singletonPartition S b,arcPartition T (qa::qs)]

/-- Universal original-AF cover for type3(i), under explicit actual local
subtree and b--c path hypotheses. Arbitrary orientation of target edges is
covered by q/r membership in the original path-pendant list. -/
theorem actual_typeI_cover {T S X U V W : Tree} {w qa q r z : RMAF.Vertex}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (ch : ActualCherry T a b) (hc : cuts S a b = [w ++ [false,false,true],w ++ [false,true]])
 (leafA : LeafAt T qa a)
 (qcut : q ∈ cuts T b c) (rcut : r ∈ cuts T b c)
 (lookupU : subtree T q = some U) (lookupV : subtree T r = some V)
 (lower : subtree T z = some W) (cW : c ∈ leaves W)
 (uW : ∀ x, x ∈ leaves U → x ∈ leaves W) (vW : ∀ y, y ∈ leaves V → y ∉ leaves W)
 (uX : ∀ x, x ∈ leaves U → x ∈ leaves X) (vX : ∀ y, y ∈ leaves V → y ∈ leaves X)
 (ha : agreement T S F = true) :
 ∃ P, P ∈ typeIChildren T S a b qa q r ∧ OriginalCover T S F P := by
 rcases hard2_or_b_or_bcx hnT hnS same he ch hc ha with hard | singleB | ⟨singleA,B,hB,bB,cB,_⟩
 · exact ⟨pendantPartition S a b,by simp [typeIChildren],hard⟩
 · exact ⟨singletonPartition S b,by simp [typeIChildren],F,ha,Nat.le_refl _,singleton_refinement ha singleB⟩
 · have two := cside_two_original_unused hnT hnS he qcut rcut lookupU lookupV lower cW uW vW uX vX ha hB bB cB
   rcases two with uq | ur
   · refine ⟨arcPartition T [qa,q],by simp [typeIChildren],F,ha,Nat.le_refl _,?_⟩
     apply singleton_plus_unused_refines [q] ha leafA singleA
     intro z hz
     have ez : z = q := by simpa using hz
     subst z
     rw [source_subtree_labels lookupU]
     exact uq
   · refine ⟨arcPartition T [qa,r],by simp [typeIChildren],F,ha,Nat.le_refl _,?_⟩
     apply singleton_plus_unused_refines [r] ha leafA singleA
     intro z hz
     have ez : z = r := by simpa using hz
     subst z
     rw [source_subtree_labels lookupV]
     exact ur

/-- Type3(ii) original-AF cover, preserving the entire literal original
b-side arc LIST. Its cost is qs.length+1, including the cut of a. -/
theorem actual_typeII_cover {T S X : Tree} {w qa : RMAF.Vertex}
 {qs : List RMAF.Vertex} {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (ch : ActualCherry T a b) (hc : cuts S a b = [w ++ [false,false,true],w ++ [false,true]])
 (leafA : LeafAt T qa a)
 (bside : ∀ q, q ∈ qs → ∃ U W r, q ∈ cuts T b c ∧ subtree T q = some U ∧ subtree T r = some W ∧
   (∀ x, x ∈ leaves U → x ∈ leaves X) ∧ (∀ x, x ∈ leaves U → x ∈ leaves W) ∧ b ∈ leaves W ∧ c ∉ leaves W)
 (ha : agreement T S F = true) :
 ∃ P, P ∈ typeIIChildren T S a b qa qs ∧ OriginalCover T S F P := by
 rcases hard2_or_b_or_bcx hnT hnS same he ch hc ha with hard | singleB | ⟨singleA,B,hB,bB,cB,_⟩
 · exact ⟨pendantPartition S a b,by simp [typeIIChildren],hard⟩
 · exact ⟨singletonPartition S b,by simp [typeIIChildren],F,ha,Nat.le_refl _,singleton_refinement ha singleB⟩
 · refine ⟨arcPartition T (qa::qs),by simp [typeIIChildren],F,ha,Nat.le_refl _,?_⟩
   apply singleton_plus_unused_refines qs ha leafA singleA
   intro q hq
   obtain ⟨U,W,r,cut,lookup,upper,uX,uW,bW,cW⟩ := bside q hq
   rw [source_subtree_labels lookup]
   exact bside_original_unused hnT hnS he cut lookup upper uX uW bW cW ha hB bB cB

/-- Type3(iii) original-AF cover. The actual incoming LCA arc is q; no
root arc is invented (the operational caller must check q nonempty). -/
theorem actual_typeIII_cover {T S X W C : Tree} {w qa q r : RMAF.Vertex}
 {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b)))
 (ch : ActualCherry T a b) (hc : cuts S a b = [w ++ [false,false,true],w ++ [false,true]])
 (leafA : LeafAt T qa a)
 (lookup : subtree T q = some W) (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bW : b ∈ leaves W) (cW : c ∈ leaves W) (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (onPath : q ∈ minimalVertices [b,c] T)
 (ha : agreement T S F = true) :
 ∃ P, P ∈ typeIIChildren T S a b qa [q] ∧ OriginalCover T S F P := by
 rcases hard2_or_b_or_bcx hnT hnS same he ch hc ha with hard | singleB | ⟨singleA,B,hB,bB,cB,_⟩
 · exact ⟨pendantPartition S a b,by simp [typeIIChildren],hard⟩
 · exact ⟨singletonPartition S b,by simp [typeIIChildren],F,ha,Nat.le_refl _,singleton_refinement ha singleB⟩
 · refine ⟨arcPartition T [qa,q],by simp [typeIIChildren],F,ha,Nat.le_refl _,?_⟩
   apply singleton_plus_unused_refines [q] ha leafA singleA
   intro z hz
   have ez : z = q := by simpa using hz
   subst z
   rw [source_subtree_labels lookup]
   exact ancestor_original_unused hnT hnS he lookup core coreLabels bW cW bC cC onPath
     ha singleA hB bB cB (unordered_cherry_distinct hnT ch)
end Universal233.Rule5Case322
