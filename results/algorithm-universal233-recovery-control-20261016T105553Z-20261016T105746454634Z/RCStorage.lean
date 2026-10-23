import RCInterface
namespace OrdinaryDispatch.RecoveryControlBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

/-- Constructor/list/bit-cell potential, not a runtime heap-address encoder. -/
def groupsCells : List BitGroup→Nat
 | []=>0
 | g::gs=>groupCells g+1+groupsCells gs

theorem groupsCells_bound (W N : Nat) (gs : List BitGroup) (caps : GroupCaps W N gs) :
 groupsCells gs≤((W+4)*N+1)*gs.length := by
 induction gs with
 | nil=>simp [groupsCells]
 | cons g gs ih=>
  have a:=group_cells_cap W N g (caps g (by simp))
  have b:=ih (by intro x hx;exact caps x (by simp [hx]))
  simp only [groupsCells,List.length_cons,Nat.mul_add,Nat.mul_one]
  omega

theorem groupsBits_retained (W N : Nat) (t : BitTree) (words : TreeWords W t) (shape : footprint (viewTree t)≤N) :
 groupsCells (groupsBits t).value≤((W+4)*N+1)*N := by
 rw [groupsBits_value]
 exact Nat.le_trans (groupsCells_bound W N _ (rawGroups_caps W N t words shape))
  (Nat.mul_le_mul_left _ (Nat.le_trans (rawGroups_length t) shape))

theorem filterColor_retained (W N : Nat) (color : List Bool) (gs : List BitGroup)
 (caps : GroupCaps W N gs) (size : gs.length≤N) :
 groupsCells (filterColor color gs).value≤((W+4)*N+1)*N :=
 Nat.le_trans (groupsCells_bound W N _ (filterColor_caps W N color gs caps))
  (Nat.mul_le_mul_left _ (Nat.le_trans (filterColor_length color gs) size))

theorem mixedBits_retained (W N : Nat) (t : BitTree) (words : TreeWords W t) (shape : footprint (viewTree t)≤N)
 (a b : BitGroup) (h : (mixedBits t).value=some (a,b)) :
 groupCells a+groupCells b+1≤2*((W+4)*N)+1 := by
 have caps:=mixedBits_caps W N t words shape a b h
 have x:=group_cells_cap W N a caps.1;have y:=group_cells_cap W N b caps.2
 omega
end OrdinaryDispatch.RecoveryControlBits
