import PaidRulesV3
open RMAF ForestState Universal233 Universal233.CherryBranching OrdinaryDispatch
namespace IndependentPaid

def refinesCheck (F Q : Forest) : Bool :=
 F.all (fun B=>Q.any (fun U=>B.all (fun x=>U.contains x)))

theorem refinesCheck_iff (F Q : Forest) : refinesCheck F Q=true ↔ VertexGeometry.Refines F Q := by
 simp only [refinesCheck,VertexGeometry.Refines,List.all_eq_true,List.any_eq_true,List.contains_iff_mem]

def oneT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def oneS : Tree := .node (.node (.leaf 0) (.leaf 2)) (.leaf 1)
def twoT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def twoS : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 3)) (.leaf 1)

theorem one_exchange_control :
 (cuts oneS 0 1).length=1 ∧ agreement oneT oneS [[0,2],[1]]=true ∧
 refinesCheck [[0,2],[1]] (pendantChild oneS 0 1).partition=false ∧
 agreement oneT oneS [[0,1],[2]]=true ∧
 refinesCheck [[0,1],[2]] (pendantChild oneS 0 1).partition=true := by decide

theorem one_original_needs_exchange :
 ¬feasible oneT oneS (pendantChild oneS 0 1) [[0,2],[1]] := by
 intro h
 have yes := (refinesCheck_iff _ _).2 h.2
 have no := one_exchange_control.2.2.1
 rw [no] at yes
 contradiction

theorem two_not_one_control :
 (cuts twoS 0 1).length=2 ∧ agreement twoT twoS [[0],[1,2,3]]=true ∧
 (pendantChild twoS 0 1).partition.length=3 := by decide

theorem two_needs_three_refining_blocks (F : Forest)
 (h : feasible twoT twoS (pendantChild twoS 0 1) F) : 3≤F.length := by
 have ns : (leaves twoS).Nodup := by decide
 have part : partitionCheck (leaves twoS) (pendantChild twoS 0 1).partition=true := by decide
 have fp := h.1
 simp only [agreement,Bool.and_eq_true] at fp
 have len := refinement_length _ F _ ns fp.1.1.1.2 part h.2
 exact len

theorem two_pendant_exchange_at_two_refuted :
 ¬∃H,feasible twoT twoS (pendantChild twoS 0 1) H ∧ H.length≤2 := by
 rintro ⟨H,hH,bound⟩
 have low := two_needs_three_refining_blocks H hH
 omega

theorem best_control :
 best id (fun x : Nat=>x != 7) [4,2,2,7]=some 2 ∧
 best id (fun x : Nat=>x != 0) [0,3,4]=some 3 ∧
 best id (fun _ : Nat=>false) [0,0]=none := by decide

theorem zero_paid_refusal : remaining 0 (pendantChild oneS 0 1)=none := by decide

theorem zero_callback_not_called :
 childCall (fun _ _=>some ([[999]] : Forest)) 0 (pendantChild oneS 0 1)=none := by decide

theorem zero_children_no_forest_execution :
 runChildren (fun _ _ _=>some ([[999]] : Forest)) oneT oneS 0 [pendantChild oneS 0 1]=none := by decide

theorem equal_budget_own_paid_refuses (T S : Tree) (q : Nat) :
 IndependentReconstruction.OwnPaid q T S q=none := by
 unfold IndependentReconstruction.OwnPaid
 split
 · rename_i impossible
   exact False.elim (Nat.lt_irrefl q impossible)
 · rfl
end IndependentPaid
