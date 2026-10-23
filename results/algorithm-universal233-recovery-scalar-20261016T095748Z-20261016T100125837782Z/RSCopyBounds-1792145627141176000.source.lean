import RSInterface
namespace OrdinaryDispatch.RecoveryBits
open Universal233 CoreProgram CoreWork
open OrdinaryDispatch.RecoveryScalar

def TreeWords (W : Nat) : BitTree→Prop
 | .leaf g=>(∀b∈g.labels,b.length≤W) ∧ g.color.length≤W
 | .node _ l r=>TreeWords W l ∧ TreeWords W r

theorem arrayCells_bound (W : Nat) (xs : List (List Bool)) (h : ∀b∈xs,b.length≤W) :
 arrayCells xs≤(W+1)*xs.length := by
 induction xs with
 | nil=>simp [arrayCells]
 | cons b bs ih=>
  have a:=h b (by simp)
  have tail:=ih (by intro c hc;exact h c (by simp [hc]))
  simp only [arrayCells,List.length_cons,Nat.mul_add,Nat.mul_one];omega

theorem treeCells_source_bound (W : Nat) (t : BitTree) (h : TreeWords W t) :
 treeCells t≤(W+4)*footprint (viewTree t) := by
 induction t with
 | leaf g=>
  have a:=arrayCells_bound W g.labels h.1
  have color:=h.2
  have labelScale:=Nat.mul_le_mul_right g.labels.length (show W+1≤W+4 by omega)
  have addrScale:=Nat.mul_le_mul_right g.origin.length (show 1≤W+4 by omega)
  simp only [treeCells,groupCells,viewTree,viewGroup,footprint,List.length_map,Nat.mul_add,Nat.mul_one,Nat.one_mul] at *
  omega
 | node p l r il ir=>
  have a:=il h.1;have b:=ir h.2
  have addrScale:=Nat.mul_le_mul_right p.length (show 1≤W+4 by omega)
  simp only [treeCells,viewTree,footprint,Nat.mul_add,Nat.mul_one,Nat.one_mul] at *
  omega

/-- Concrete complete represented-tree copy, with source footprint cap. This
pays this copy invocation only; there is no whole-run lifetime simulation. -/
theorem copyTree_source_bound (W N B q : Nat) (t : BitTree) (d : List Group) (c : List RMAF.Vertex)
 (words : TreeWords W t) (caps : StateCap N B q (viewTree t) d c) :
 (copyTree t).work≤64*(W+4)*N := by
 have a:=copyTree_work t
 have b:=treeCells_source_bound W t words
 have within:=caps.within;dsimp only [Within] at within
 have fp:footprint (viewTree t)≤N:=by omega
 have z:=Nat.le_trans b (Nat.mul_le_mul_left (W+4) fp)
 exact Nat.le_trans a (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 64 z)

def ForestWords (W : Nat) (P : List (List (List Bool))) : Prop := ∀b∈P,∀x∈b,x.length≤W

theorem forestCells_bound (W : Nat) (P : List (List (List Bool))) (h : ForestWords W P) :
 forestCells P≤(W+1)*P.flatten.length+P.length := by
 induction P with
 | nil=>simp [forestCells]
 | cons b P ih=>
  have a:=arrayCells_bound W b (h b (by simp))
  have tail:=ih (by intro c hc x hx;exact h c (by simp [hc]) x hx)
  simp only [forestCells,List.flatten_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one] at *
  omega

/-- Complete represented output materialization has a derived polynomial bill.
It does not stand in for producing every output of the recursive generator. -/
theorem copyOutput_source_bound (W N B : Nat) (o : BitOutput)
 (words : ForestWords W o.partition) (caps : OutputCap N B (viewOutput o)) :
 (copyOutput o).work≤32*(W+4)*(N+1)^2 := by
 have copy:=copyOutput_work o
 have forest:=forestCells_bound W o.partition words
 have addresses:=arrayCells_bound N o.sourceCuts caps.addresses
 have flat:=output_flatten_cap N B (viewOutput o) caps
 have flat_eq:(viewOutput o).partition.flatten.length=o.partition.flatten.length:=by
  change (o.partition.map (List.map decode)).flatten.length=o.partition.flatten.length
  have aux (P : List (List (List Bool))) : (P.map (List.map decode)).flatten.length=P.flatten.length:=by
   induction P with
   | nil=>rfl
   | cons b P ih=>simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_map,ih]
  exact aux o.partition
 rw [flat_eq] at flat
 have plen:o.partition.length≤N+1:=by simpa only [viewOutput,List.length_map] using caps.blocks
 have clen:o.sourceCuts.length≤N:=caps.cuts
 let K:=(N+1)^2
 have sq:N*(N+1)≤K:=by dsimp only [K];rw [Nat.pow_two];exact Nat.mul_le_mul_right (N+1) (Nat.le_succ N)
 have one:1≤K:=Nat.one_le_pow _ _ (by omega)
 have linear:N+1≤K:=by
  dsimp only [K];rw [Nat.pow_two]
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right (N+1) (show 1≤N+1 by omega)
 have f:forestCells o.partition≤(W+1)*K+K:=by
  have s:=Nat.mul_le_mul_left (W+1) (Nat.le_trans flat sq)
  omega
 have a:arrayCells o.sourceCuts≤K:=by
  have z:=Nat.mul_le_mul_left (N+1) clen
  have eq:(N+1)*N=N*(N+1):=Nat.mul_comm _ _
  rw [eq] at z
  omega
 have total:outputCells o≤(W+4)*K:=by
  simp only [outputCells]
  have eq:(W+4)*K=(W+1)*K+3*K:=by simp only [Nat.add_mul,Nat.one_mul];omega
  rw [eq]
  omega
 exact Nat.le_trans copy (by simpa only [K,Nat.mul_assoc] using Nat.mul_le_mul_left 32 total)
end OrdinaryDispatch.RecoveryBits
