import OwnerCost
namespace AllGoodDP.LocalWork
open RMAF Universal233.WholeSourceWork Universal233.CoreWork

def meterSolve (cs : List Nat) (owner : Nat→Charged Nat) (t : Tree) : Charged Paint :=
 let tab := meterTable cs owner t
 let pick := meterChoose meterChanges tab.value
 ⟨pick.value,tab.work+pick.work+8⟩
@[simp] theorem meterSolve_value (cs : List Nat) (owner : Nat→Charged Nat) (t : Tree) :
 (meterSolve cs owner t).value=solve cs (fun x=>(owner x).value) t := by simp [meterSolve,solve]

def solveBill (C m N : Nat) : Nat := tableCoefficient C m N*N+(32*N+12)*(m+1)+16

theorem meterSolve_work (cs : List Nat) (owner : Nat→Charged Nat) (t : Tree) (hc : cs≠[]) (C N : Nat)
 (ht : treeNodes t≤N) (ho : ∀x,x∈leaves t→(owner x).work≤C) :
 (meterSolve cs owner t).work≤solveBill C cs.length N := by
 have tablework := meterTable_work cs owner t hc C N ht ho
 have point : ∀p,p∈table cs (fun x=>(owner x).value) t→(meterChanges p).work≤16*N := by
  intro p hp
  have sz : paintNodes p=treeNodes t := by rw [paintNodes_erase,table_erase cs (fun x=>(owner x).value) t hc p hp]
  exact Nat.le_trans (meterChanges_work p) (by rw [sz];exact Nat.mul_le_mul_left 16 ht)
 have pick := meterChoose_work meterChanges (table cs (fun x=>(owner x).value) t) (16*N) point
 have len : (table cs (fun x=>(owner x).value) t).length≤cs.length+1 := by rw [table_length];cases t <;> simp
 have eq : 2*(16*N)+12=32*N+12 := by omega
 rw [eq] at pick
 have mul := Nat.mul_le_mul_left (32*N+12) len
 have mul2 := Nat.mul_le_mul_left (tableCoefficient C cs.length N) ht
 simp only [meterSolve,meterTable_value,solveBill]
 omega

theorem meterSolve_erase (cs : List Nat) (owner : Nat→Charged Nat) (t : Tree) (hc : cs≠[]) :
 erase (meterSolve cs owner t).value=t := by
 rw [meterSolve_value]
 exact table_erase cs (fun x=>(owner x).value) t hc _
  (choose_spec changes (table cs (fun x=>(owner x).value) t) (table_nonempty cs _ t hc)).1

theorem chooseCap_mono {m n M N : Nat} (hm : m≤M) (hn : n≤N) : chooseCap m n≤chooseCap M N := by
 have mul := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 48 hn) 12) (Nat.add_le_add_right hm 1)
 exact Nat.add_le_add_right mul 8

theorem tableCoefficient_mono {C D m n M N : Nat} (hC : C≤D) (hm : m≤M) (hn : n≤N) :
 tableCoefficient C m n≤tableCoefficient D M N := by
 have ch := chooseCap_mono hm hn
 have mul := Nat.mul_le_mul hm (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ch) 8)
 simp only [tableCoefficient,nodeCharge]
 omega

theorem solveBill_mono {C D m n M N : Nat} (hC : C≤D) (hm : m≤M) (hn : n≤N) : solveBill C m n≤solveBill D M N := by
 have a := Nat.mul_le_mul (tableCoefficient_mono hC hm hn) hn
 have b := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 32 hn) 12) (Nat.add_le_add_right hm 1)
 simp only [solveBill]
 omega
end AllGoodDP.LocalWork
