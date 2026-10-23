import RWRun
namespace OrdinaryDispatch.RecoveryLocalWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.OptimizerLocalWork

structure Built where
 value : GTree
 work : Nat
 coloring : Nat

def meterBuild (color : Nat→Charged Nat) (p : RMAF.Vertex) : Tree→Built
 | .leaf x=>let a:=color x;⟨.leaf ⟨p,[x],a.value⟩,a.work+8,a.work⟩
 | .node l r=>let a:=meterBuild color (p++[false]) l;let b:=meterBuild color (p++[true]) r
   ⟨.node p a.value b.value,a.work+b.work+8*(p.length+1)+8,a.coloring+b.coloring⟩
@[simp] theorem meterBuild_value (color p t) :
 (meterBuild color p t).value=fromTree (fun x=>(color x).value) p t := by
 induction t generalizing p <;> simp_all [meterBuild,fromTree]

theorem meterBuild_coloring (color p t) :
 (meterBuild color p t).coloring=((leaves t).map (fun x=>(color x).work)).sum := by
 induction t generalizing p <;> simp_all [meterBuild,leaves,List.map_append,List.sum_append]

theorem meterBuild_bound (color : Nat→Charged Nat) (p : RMAF.Vertex) (t : Tree) (N : Nat)
 (size : p.length+treeNodes t≤N) :
 (meterBuild color p t).work≤32*(N+1)*treeNodes t+(meterBuild color p t).coloring := by
 induction t generalizing p with
 | leaf x=>simp only [meterBuild,treeNodes,Nat.mul_one];omega
 | node l r il ir=>
  have ls : (p++[false]).length+treeNodes l≤N:=by simp only [List.length_append,List.length_cons,List.length_nil,treeNodes] at size ⊢;omega
  have rs : (p++[true]).length+treeNodes r≤N:=by simp only [List.length_append,List.length_cons,List.length_nil,treeNodes] at size ⊢;omega
  have a:=il (p++[false]) ls;have b:=ir (p++[true]) rs
  simp only [meterBuild,treeNodes,Nat.mul_add,Nat.mul_one] at *;omega

structure InitialMeasured where
 value : Option (Nat×GTree)
 work : Nat
 coloring : Nat

def meterInitial (color : Nat→Charged Nat) (budget : Nat) (t : Tree) : InitialMeasured :=
 let leaves1:=meterLeaves t;let proper:=meterNodup leaves1.value
 if proper.value then
  let leaves2:=meterLeaves t;let len:=meterLength leaves2.value
  let built:=meterBuild color [] t
  ⟨some (min budget (len.value-1),built.value),leaves1.work+proper.work+leaves2.work+len.work+built.work+16,built.coloring⟩
 else ⟨none,leaves1.work+proper.work+8,0⟩
@[simp] theorem meterInitial_value (color budget t) :
 (meterInitial color budget t).value=
 (if (leaves t).Nodup then some (min budget ((leaves t).length-1),fromTree (fun x=>(color x).value) [] t) else none) := by
 by_cases h:(leaves t).Nodup <;> simp [meterInitial,h]

theorem meterInitial_coloring (color budget t) :
 (meterInitial color budget t).coloring=
 (if (leaves t).Nodup then ((leaves t).map (fun x=>(color x).work)).sum else 0) := by
 by_cases h:(leaves t).Nodup <;> simp [meterInitial,h,meterBuild_coloring]

/-- The frozen initialCharge now follows from actual leaves/nodup/length/min/
address-append/fromTree operations, with oracle coloring added separately. -/
theorem meterInitial_bound (color : Nat→Charged Nat) (budget : Nat) (t : Tree) :
 (meterInitial color budget t).work≤CoreWork.initialCharge t+(meterInitial color budget t).coloring := by
 let N:=treeNodes t
 have leaf:=meterLeaves_cap t N (Nat.le_refl _)
 have len:=leaves_nodes t
 have nodup:=Nat.le_trans (meterNodup_bound (leaves t))
  (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right len 1) 2))
 have length:=meterLength_work (leaves t)
 have build:=meterBuild_bound color [] t N (by simp [N])
 have buildcap:=Nat.mul_le_mul_left (32*(N+1)) (Nat.le_succ N)
 have p1 : N+1≤(N+1)^3:=by simpa using pow_mono N 1 3 (by decide)
 have p2:=pow_mono N 2 3 (by decide)
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 have l3:=cap_lift N 8 2 3 _ leaf (by decide)
 have n3:=cap_lift N 8 2 3 _ nodup (by decide)
 have b3 : (meterBuild color [] t).work≤32*(N+1)^3+(meterBuild color [] t).coloring := by
  have bound : 32*(N+1)*N≤32*(N+1)^2:=by simpa only [Nat.pow_two,Nat.mul_assoc] using buildcap
  have lift:=Nat.mul_le_mul_left 32 p2;omega
 simp only [meterInitial,meterLeaves_value,CoreWork.initialCharge]
 split <;> simp only [InitialMeasured.work,InitialMeasured.coloring]
 · change _≤128*(N+1)^3+_;change (leaves t).length≤N at len;omega
 · change _≤128*(N+1)^3+_;omega

def meterGenerate (t : Tree) (color : Nat→Charged Nat) (budget : Nat) : Charged Receipt :=
 let init:=meterInitial color budget t
 match init.value with
 | none=>⟨⟨[],["duplicate original label"],0,0,0⟩,init.work+8⟩
 | some (q,built)=>let r:=meterRun q built [] [];⟨r.value,init.work+r.work+8⟩
@[simp] theorem meterGenerate_value (t color budget) :
 (meterGenerate t color budget).value=CoreProgram.generate t (fun x=>(color x).value) budget := by
 simp only [meterGenerate,meterInitial_value,CoreProgram.generate]
 split <;> simp only [meterRun_value]

theorem meterGenerate_bound (t : Tree) (color : Nat→Charged Nat) (budget : Nat) :
 (meterGenerate t color budget).work≤initialCharge t+
  16*((localCap (inputResource t)+6)*(min budget ((leaves t).length-1)+1)*
    2^(min budget ((leaves t).length-1)+1))+
  ((leaves t).map (fun x=>(color x).work)).sum+8 := by
 have init:=meterInitial_bound color budget t
 have coloring:=meterInitial_coloring color budget t
 have within:=initial_within t (fun x=>(color x).value) budget
 have run:=meterRun_closed (min budget ((leaves t).length-1)) (inputResource t)
  (fromTree (fun x=>(color x).value) [] t) [] [] within
 simp only [meterGenerate,meterInitial_value]
 by_cases h:(leaves t).Nodup
 · simp only [h,ite_true] at coloring ⊢;omega
 · simp only [h,ite_false] at coloring ⊢;omega
end OrdinaryDispatch.RecoveryLocalWork
