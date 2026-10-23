import PaidRootBoundary
namespace Universal233.Case322PaidGuard
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction
set_option maxRecDepth 24000

/-- Universal current paid guards from original source/core geometry and the
actual outgoing core boundary. The stronger exact Figure15.2 frontier is bound
below. No saving, cover, component count or guard is an input. -/
theorem rawPlan_currentGuards_outgoing {T S X C : Tree}
 {w r qa ub uc : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (ch : ActualCherry T a b)
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C)
 (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (rnr : r ≠ []) (tailHull : r.dropLast ∈ minimalVertices (leaves X) T) :
 (rawPlan T S a b c qa (bArc w sb) ub uc).all (currentGuard T S) = true := by
 have proper := bottom_proper hnS he
 have hab : a ≠ b := by
   intro e
   exact proper.2.2.2 ((VC_mem sa sc a c b X).2 (Or.inl e.symm))
 have hbc : b ≠ c := by
   intro e
   exact proper.2.2.2 ((VC_mem sa sc a c b X).2 (Or.inr (Or.inr e)))
 have hac := proper.2.2.1
 have ar : a ∈ subtreeLabels T r := by
   rw [source_subtree_labels core]
   exact (coreLabels a (leafAt_label T qa a la)).2 ⟨proper.1,hac⟩
 have br : b ∈ subtreeLabels T r := by rw [source_subtree_labels core]; exact bC
 have xSub : ∀ x, x ∈ leaves X → x ∈ leaves T := by
   intro x hx
   apply (same x).2
   apply (subtreeLabels_sublist S (xArc w sa sc sb)).subset
   rw [source_subtree_labels (bottom_x_lookup he)]
   exact hx
 have disj : ∀ x, x ∈ leaves X → x ∉ subtreeLabels T r := by
   intro x hx hin
   rw [source_subtree_labels core] at hin
   exact ((coreLabels x (xSub x hx)).1 hin).1 hx
 have sourceA : a ∈ leaves S := leafAt_label S _ a (bottom_a_lookup he)
 have hard := hardBranch_currentGuard (T:=T) (b:=b) hnS sourceA
 have bguard := bBranch_currentGuard (T:=T) hnS (bottom_b_lookup he) sourceA hab.symm
 have cGuard : ∀ q, q ∈ cSideEdges T b c → currentGuard T S (targetBranch T [qa,q]) = true := by
   intro q hq; exact cside_branch_currentGuard hnT ch la lb lc hab hac hbc hq
 have bGuard := bside_branch_currentGuard (S:=S) hnT ch la lb lc hab hac hbc
 have lGuard : bSideWithoutA T a b c = [] →
     currentGuard T S (targetBranch T [qa,lca ub uc]) = true := by
   intro empty
   have nr := fallback_lca_nonroot hnT la lb lc ⟨C,core⟩ rnr ar br xSub disj tailHull empty
   obtain ⟨W,lookup,bW,cW,_⟩ := actual_lca_geometry hnT lb lc
   apply ancestor_branch_currentGuard hnT ch la lb lc hab hbc ⟨W,lookup⟩ nr
   · rw [source_subtree_labels lookup]; exact bW
   · rw [source_subtree_labels lookup]; exact cW
 have rest : (match bSideWithoutA T a b c with
     | [] => typeIIBranches T S a b qa (bArc w sb) [lca ub uc]
     | qs => typeIIBranches T S a b qa (bArc w sb) qs).all (currentGuard T S) = true := by
   cases eb : bSideWithoutA T a b c with
   | nil => simp [typeIIBranches,hard,bguard,lGuard eb]
   | cons q qs =>
     have h := bGuard
     rw [eb] at h
     simp [typeIIBranches,hard,bguard,h]
 cases ei : cSideEdges T b c with
 | nil => cases eb : bSideWithoutA T a b c <;> simpa [rawPlan,ei,eb] using rest
 | cons q tail =>
   cases tail with
   | nil => cases eb : bSideWithoutA T a b c <;> simpa [rawPlan,ei,eb] using rest
   | cons t tail =>
     have qg := cGuard q (by simp [ei])
     have tg := cGuard t (by simp [ei])
     simp [rawPlan,ei,typeIBranches,hard,bguard,qg,tg]

/-- Exact consuming signature from the extraction freeze, including both
frontier orders, all sibling bits, and ordinary original-root semantics. -/
theorem literal_rawPlan_currentGuards {T S X C : Tree}
 {w r qa ub uc : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (ch : ActualCherry T a b) (_two : (cuts S a b).length = 2)
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (_cC : c ∉ leaves C)
 (la : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (frontier : incident T (leaves X) = [r,uc] ∨ incident T (leaves X) = [uc,r])
 (tailR : r.dropLast ∈ minimalVertices (leaves X) T)
 (_tailC : uc.dropLast ∈ minimalVertices (leaves X) T)
 (_offR : r ∉ minimalVertices (leaves X) T) (_offC : uc ∉ minimalVertices (leaves X) T) :
 ∀ child, child ∈ rawPlan T S a b c qa (bArc w sb) ub uc → currentGuard T S child = true := by
 have mem : r ∈ incident T (leaves X) := by rcases frontier with h | h <;> simp [h]
 have nr := ((incident_spec T (leaves X) r).1 mem).2.1
 exact List.all_eq_true.1 (rawPlan_currentGuards_outgoing hnT hnS same he ch core coreLabels bC la lb lc nr tailR)

end Universal233.Case322PaidGuard
