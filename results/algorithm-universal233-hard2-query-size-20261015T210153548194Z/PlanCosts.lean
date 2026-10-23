import CurrentPartition
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322

theorem rawPlan_cost_classes {T S : Tree} {a b c : Nat} {qa qb ub uc : RMAF.Vertex}
 (two : (cuts S a b).length = 2) :
 (rawPlan T S a b c qa qb ub uc).map paid = [2,1,2,2] ∨
 ∃ d, 2 ≤ d ∧ (rawPlan T S a b c qa qb ub uc).map paid = [2,1,d] := by
 cases ec : cSideEdges T b c with
 | nil =>
   cases eb : bSideWithoutA T a b c with
   | nil => right; exact ⟨2,by decide,by simp [rawPlan,ec,eb,typeII_raw_costs two]⟩
   | cons q qs => right; exact ⟨qs.length+2,by omega,by simp [rawPlan,ec,eb,typeII_raw_costs two]⟩
 | cons q qs =>
   cases qs with
   | nil =>
     cases eb : bSideWithoutA T a b c with
     | nil => right; exact ⟨2,by decide,by simp [rawPlan,ec,eb,typeII_raw_costs two]⟩
     | cons t ts => right; exact ⟨ts.length+2,by omega,by simp [rawPlan,ec,eb,typeII_raw_costs two]⟩
   | cons t ts => left; simp [rawPlan,ec,typeI_raw_costs two]

theorem rawPlan_cost_positive {T S : Tree} {a b c : Nat} {qa qb ub uc : RMAF.Vertex}
 (two : (cuts S a b).length = 2) : ∀ child, child ∈ rawPlan T S a b c qa qb ub uc → 0 < paid child := by
 intro child hc
 have mem : paid child ∈ (rawPlan T S a b c qa qb ub uc).map paid := List.mem_map.2 ⟨child,hc,rfl⟩
 rcases rawPlan_cost_classes (T:=T) (S:=S) (a:=a) (b:=b) (c:=c) (qa:=qa) (qb:=qb) (ub:=ub) (uc:=uc) two with h | ⟨d,hd,h⟩
 · rw [h] at mem; simp at mem; omega
 · rw [h] at mem; simp at mem; omega

theorem rawPlan_callbacks_decrease {T S : Tree} {a b c q n : Nat} {qa qb ub uc : RMAF.Vertex}
 (two : (cuts S a b).length = 2)
 (mem : n ∈ callbackRequests q (rawPlan T S a b c qa qb ub uc)) : n < q :=
 callback_strict_decrease (rawPlan_cost_positive two) mem

/-- A typeII list can cost four or more. Monotone weights bound its literal
list mass without changing that cost or merging callback occurrences. -/
theorem rawPlan_LIST_mass_bound {T S : Tree} {a b c : Nat} {qa qb ub uc : RMAF.Vertex}
 (two : (cuts S a b).length = 2) (weight : Nat → Nat)
 (decay : ∀ d, 2 ≤ d → weight d ≤ weight 2) :
 rawMass weight ((rawPlan T S a b c qa qb ub uc).map paid) ≤ weight 1+3*weight 2 := by
 rcases rawPlan_cost_classes (T:=T) (S:=S) (a:=a) (b:=b) (c:=c) (qa:=qa) (qb:=qb) (ub:=ub) (uc:=uc) two with h | ⟨d,hd,h⟩
 · rw [h,typeI_LIST_mass]; exact Nat.le_refl _
 · rw [h]
   have le := decay d hd
   simp only [rawMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
   omega
end Universal233.Case322Extraction
