import PrefixLeaves
namespace Universal233.Rule5PrefixLocalWork
open RMAF

def nodupTreeMeter (T : Tree) : Measured Bool :=
 let l:=leavesMeter T;let d:=nodupMeter l.value
 ⟨d.value,l.work+d.work+1⟩

def containsTreeMeter (T : Tree) (x : Nat) : Measured Bool :=
 let l:=leavesMeter T;let d:=containsMeter x l.value
 ⟨d.value,l.work+d.work+1⟩

/-- Conservatively re-extract the captured leaf list at every predicate call.
This pays all source copies even if the compiler shares the original closure. -/
def allTreeMeter (S : Tree) : List Nat→Measured Bool
 | []=>⟨true,1⟩
 | x::xs=>let c:=containsTreeMeter S x
          if c.value then let r:=allTreeMeter S xs;⟨r.value,c.work+r.work+1⟩
          else ⟨false,c.work+1⟩

def allPairMeter (T S : Tree) : Measured Bool :=
 let l:=leavesMeter T;let a:=allTreeMeter S l.value
 ⟨a.value,l.work+a.work+1⟩

theorem nodup_tree_value (T : Tree) : (nodupTreeMeter T).value=decide (leaves T).Nodup := by
 simp only [nodupTreeMeter,nodup_value,leaves_value]

theorem contains_tree_value (T : Tree) (x : Nat) : (containsTreeMeter T x).value=(leaves T).contains x := by
 simp only [containsTreeMeter,contains_value,leaves_value]

theorem all_tree_value (S : Tree) (A : List Nat) : (allTreeMeter S A).value=A.all (leaves S).contains := by
 induction A with
 | nil=>rfl
 | cons x A ih=>simp only [allTreeMeter,List.all_cons,contains_tree_value];split <;> simp_all

theorem all_pair_value (T S : Tree) : (allPairMeter T S).value=(leaves T).all (leaves S).contains := by
 simp only [allPairMeter,all_tree_value,leaves_value]

theorem nodup_tree_work (T : Tree) :
 (nodupTreeMeter T).work≤8*((leaves T).length+1)*((leaves T).length+1) := by
 have l:=leaves_work T
 have n:=nodup_work (leaves T)
 simp only [nodupTreeMeter,leaves_value]
 simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] at *
 omega

theorem contains_tree_work (T : Tree) (x : Nat) :
 (containsTreeMeter T x).work≤4*(leaves T).length*(leaves T).length+2*(leaves T).length+2 := by
 have l:=leaves_work T
 have c:=contains_work x (leaves T)
 simp only [containsTreeMeter,leaves_value]
 omega

theorem all_tree_work (S : Tree) (A : List Nat) :
 (allTreeMeter S A).work≤(4*(leaves S).length*(leaves S).length+2*(leaves S).length+3)*A.length+1 := by
 induction A with
 | nil=>simp [allTreeMeter]
 | cons x A ih=>
   have c:=contains_tree_work S x
   simp only [allTreeMeter]
   split <;> simp only [List.length_cons,Nat.mul_succ] <;> omega

theorem all_pair_work (T S : Tree) :
 (allPairMeter T S).work≤4*(leaves T).length*(leaves T).length+
  (4*(leaves S).length*(leaves S).length+2*(leaves S).length+3)*(leaves T).length+2 := by
 have l:=leaves_work T
 have a:=all_tree_work S (leaves T)
 simp only [allPairMeter,leaves_value]
 omega

/-- Literal properPair short-circuit order, including false/refused guards.
The extra leaf extraction within a contains predicate is conservative. -/
def properPairMeter (T S : Tree) : Measured Bool :=
 let a:=nodupTreeMeter T
 if a.value then
  let b:=nodupTreeMeter S
  if b.value then
   let c:=allPairMeter T S
   if c.value then
    let d:=allPairMeter S T
    ⟨d.value,a.work+b.work+c.work+d.work+4⟩
   else ⟨false,a.work+b.work+c.work+3⟩
  else ⟨false,a.work+b.work+2⟩
 else ⟨false,a.work+1⟩

theorem proper_pair_value (T S : Tree) : (properPairMeter T S).value=Rule5Local.properPair T S := by
 simp only [properPairMeter,Rule5Local.properPair,nodup_tree_value,all_pair_value]
 split <;> simp_all
 split <;> simp_all
 split <;> simp_all

def properPolynomial (N : Nat) : Nat :=
 16*(N+1)*(N+1)+8*N*N+2*(4*N*N+2*N+3)*N+8

theorem proper_pair_work (T S : Tree) (N : Nat)
 (ht : (leaves T).length≤N) (hs : (leaves S).length≤N) :
 (properPairMeter T S).work≤properPolynomial N := by
 have nt:=nodup_tree_work T
 have ns:=nodup_tree_work S
 have ts:=all_pair_work T S
 have st:=all_pair_work S T
 have tt:=Nat.mul_le_mul ht ht
 have ss:=Nat.mul_le_mul hs hs
 have t1:=Nat.mul_le_mul (Nat.add_le_add_right ht 1) (Nat.add_le_add_right ht 1)
 have s1:=Nat.mul_le_mul (Nat.add_le_add_right hs 1) (Nat.add_le_add_right hs 1)
 have tpol : 4*(leaves T).length*(leaves T).length+2*(leaves T).length+3≤4*N*N+2*N+3 := by
   have:=Nat.mul_le_mul_left 4 tt
   simp only [Nat.mul_assoc] at *
   omega
 have spol : 4*(leaves S).length*(leaves S).length+2*(leaves S).length+3≤4*N*N+2*N+3 := by
   have:=Nat.mul_le_mul_left 4 ss
   simp only [Nat.mul_assoc] at *
   omega
 have tp:=Nat.mul_le_mul spol ht
 have sp:=Nat.mul_le_mul tpol hs
 have nt' :=Nat.mul_le_mul_left 8 t1
 have ns' :=Nat.mul_le_mul_left 8 s1
 have tt' :=Nat.mul_le_mul_left 4 tt
 have ss' :=Nat.mul_le_mul_left 4 ss
 simp only [Nat.mul_assoc] at nt ns nt' ns' tt' ss'
 unfold properPolynomial properPairMeter
 split <;> try omega
 split <;> try omega
 split <;> omega
end Universal233.Rule5PrefixLocalWork
