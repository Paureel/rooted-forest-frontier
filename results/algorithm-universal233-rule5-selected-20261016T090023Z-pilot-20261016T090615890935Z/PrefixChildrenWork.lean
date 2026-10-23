import SelectedRestriction
namespace Universal233.Rule5SelectedLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork
open CherryBranching CoreWork Rule5Classification

/-- Upper source trace of each scalar comparison/filter cell; no shared set. -/
def excludeOneMeter (x : Nat) : List Nat→Measured (List Nat)
 | []=>⟨[],1⟩
 | z::zs=>let r:=excludeOneMeter x zs;⟨if z != x then z::r.value else r.value,r.work+3⟩
def excludeTwoMeter (x y : Nat) : List Nat→Measured (List Nat)
 | []=>⟨[],1⟩
 | z::zs=>let r:=excludeTwoMeter x y zs;⟨if z != x && z != y then z::r.value else r.value,r.work+4⟩

theorem exclude_one_value (x : Nat) (zs : List Nat) :
 (excludeOneMeter x zs).value=zs.filter (fun z=>z != x) := by
 induction zs with
 | nil=>rfl
 | cons z zs ih=>simp only [excludeOneMeter,List.filter_cons,ih]
theorem exclude_two_value (x y : Nat) (zs : List Nat) :
 (excludeTwoMeter x y zs).value=zs.filter (fun z=>z != x && z != y) := by
 induction zs with
 | nil=>rfl
 | cons z zs ih=>simp only [excludeTwoMeter,List.filter_cons,ih]
theorem exclude_one_work (x : Nat) (zs : List Nat) : (excludeOneMeter x zs).work=3*zs.length+1 := by
 induction zs with
 | nil=>rfl
 | cons z zs ih=>simp only [excludeOneMeter,ih,List.length_cons];omega
theorem exclude_two_work (x y : Nat) (zs : List Nat) : (excludeTwoMeter x y zs).work=4*zs.length+1 := by
 induction zs with
 | nil=>rfl
 | cons z zs ih=>simp only [excludeTwoMeter,ih,List.length_cons];omega

def singletonPartitionMeter (S : Tree) (x : Nat) : Measured (List (List Nat)) :=
 let l:=leavesMeter S;let f:=excludeOneMeter x l.value
 ⟨[[x],f.value],l.work+f.work+5⟩
def pairPartitionMeter (S : Tree) (x y : Nat) : Measured (List (List Nat)) :=
 let l:=leavesMeter S;let f:=excludeTwoMeter x y l.value
 ⟨[[x],[y],f.value],l.work+f.work+7⟩

theorem singleton_partition_value (S : Tree) (x : Nat) :
 (singletonPartitionMeter S x).value=singletonPartition S x := by
 simp only [singletonPartitionMeter,singletonPartition,exclude_one_value,leaves_value]
theorem pair_partition_value (S : Tree) (x y : Nat) :
 (pairPartitionMeter S x y).value=pairPartition S x y := by
 simp only [pairPartitionMeter,pairPartition,exclude_two_value,leaves_value]

def singletonPartitionBudget (n : Nat) :=4*n*n+3*n+6
def pairPartitionBudget (n : Nat) :=4*n*n+4*n+8

theorem singleton_partition_work (S : Tree) (x : Nat) :
 (singletonPartitionMeter S x).work≤singletonPartitionBudget (leaves S).length := by
 have:=leaves_work S
 simp only [singletonPartitionMeter,exclude_one_work,leaves_value,singletonPartitionBudget]
 omega
theorem pair_partition_work (S : Tree) (x y : Nat) :
 (pairPartitionMeter S x y).work≤pairPartitionBudget (leaves S).length := by
 have:=leaves_work S
 simp only [pairPartitionMeter,exclude_two_work,leaves_value,pairPartitionBudget]
 omega

theorem singleton_partition_domain (S : Tree) (x : Nat) :
 (singletonPartitionMeter S x).value.length=2 ∧
 (∀B,B∈(singletonPartitionMeter S x).value →B.length≤(leaves S).length) ∧
 (singletonPartitionMeter S x).value.flatten.length≤(leaves S).length+1 := by
 have pos:=leaves_positive S
 have f:=List.length_filter_le (fun z=>z != x) (leaves S)
 rw [singleton_partition_value]
 refine ⟨rfl,?_,?_⟩
 · intro B hB
   simp only [singletonPartition,List.mem_cons,List.mem_nil_iff,or_false] at hB
   rcases hB with rfl|rfl
   · simpa using pos
   · exact f
 · simpa only [singletonPartition,List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append,List.length_singleton,Nat.add_comm] using Nat.add_le_add_right f 1

theorem pair_partition_domain (S : Tree) (x y : Nat) :
 (pairPartitionMeter S x y).value.length=3 ∧
 (∀B,B∈(pairPartitionMeter S x y).value →B.length≤(leaves S).length) ∧
 (pairPartitionMeter S x y).value.flatten.length≤(leaves S).length+2 := by
 have pos:=leaves_positive S
 have f:=List.length_filter_le (fun z=>z != x && z != y) (leaves S)
 rw [pair_partition_value]
 refine ⟨rfl,?_,?_⟩
 · intro B hB
   simp only [pairPartition,List.mem_cons,List.mem_nil_iff,or_false] at hB
   rcases hB with rfl|rfl|rfl
   · simpa using pos
   · simpa using pos
   · exact f
 · simp only [pairPartition,List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append,List.length_singleton]
   omega

/-- Only a composition of the literal partition builder and exact materializer. -/
def singletonChildMeter (S : Tree) (x : Nat) : Measured Child :=
 let p:=singletonPartitionMeter S x;let c:=makeChildMeter S p.value 1
 ⟨c.value,p.work+c.work+1⟩
def pairChildMeter (S : Tree) (x y : Nat) : Measured Child :=
 let p:=pairPartitionMeter S x y;let c:=makeChildMeter S p.value 2
 ⟨c.value,p.work+c.work+1⟩

theorem singleton_child_value (S : Tree) (x : Nat) :
 (singletonChildMeter S x).value=singletonChild S x := by
 simp only [singletonChildMeter,make_child_value,singleton_partition_value,singletonChild]
theorem pair_child_value (S : Tree) (x y : Nat) :
 (pairChildMeter S x y).value=pairChild S x y := by
 simp only [pairChildMeter,make_child_value,pair_partition_value,pairChild]

def singletonChildBudget (n : Nat) :=singletonPartitionBudget n+(4*(n+2)*(2*n)+3)*2+6
def pairChildBudget (n : Nat) :=pairPartitionBudget n+(4*(n+2)*(2*n)+3)*3+6

theorem singleton_child_work (S : Tree) (x : Nat) :
 (singletonChildMeter S x).work≤singletonChildBudget (leaves S).length := by
 have p:=singleton_partition_work S x
 have dom:=singleton_partition_domain S x
 have c:=make_child_work S (singletonPartitionMeter S x).value 1 (leaves S).length dom.2.1
 have n:=treeNodes_le_twice_leaves S
 have scale:=Nat.mul_le_mul_left (4*((leaves S).length+2)) (show treeNodes S≤2*(leaves S).length by omega)
 have mul:=Nat.mul_le_mul_right 2 (Nat.add_le_add_right scale 3)
 rw [dom.1] at c
 simp only [singletonChildMeter,singletonChildBudget]
 omega

theorem pair_child_work (S : Tree) (x y : Nat) :
 (pairChildMeter S x y).work≤pairChildBudget (leaves S).length := by
 have p:=pair_partition_work S x y
 have dom:=pair_partition_domain S x y
 have c:=make_child_work S (pairPartitionMeter S x y).value 2 (leaves S).length dom.2.1
 have n:=treeNodes_le_twice_leaves S
 have scale:=Nat.mul_le_mul_left (4*((leaves S).length+2)) (show treeNodes S≤2*(leaves S).length by omega)
 have mul:=Nat.mul_le_mul_right 3 (Nat.add_le_add_right scale 3)
 rw [dom.1] at c
 simp only [pairChildMeter,pairChildBudget]
 omega

def fiveChildrenMeter (S : Tree) (a b p q : Nat) : Measured (List Child) :=
 let c:=pendantChildMeter S a b;let pa:=pairChildMeter S p a;let pb:=pairChildMeter S p b
 let qa:=pairChildMeter S q a;let qb:=pairChildMeter S q b
 ⟨[c.value,pa.value,pb.value,qa.value,qb.value],c.work+pa.work+pb.work+qa.work+qb.work+6⟩

theorem five_children_value (S : Tree) (a b p q : Nat) :
 (fiveChildrenMeter S a b p q).value=fiveChildren S a b p q := by
 simp only [fiveChildrenMeter,fiveChildren,pendant_child_value,pair_child_value]

def fiveChildrenBudget (n : Nat) :=pendantChildBudget n+4*pairChildBudget n+6

theorem five_children_work (S : Tree) (a b p q : Nat) :
 (fiveChildrenMeter S a b p q).work≤fiveChildrenBudget (leaves S).length := by
 have c:=pendant_child_work S a b
 have pa:=pair_child_work S p a
 have pb:=pair_child_work S p b
 have qa:=pair_child_work S q a
 have qb:=pair_child_work S q b
 simp only [fiveChildrenMeter,fiveChildrenBudget]
 omega

def localChildrenMeter (S : Tree) (a b : Nat) : LocalSelection→Measured (List Child)
 | .large _=>let c:=pendantChildMeter S a b;⟨[c.value],c.work+2⟩
 | .two c=>fiveChildrenMeter S a b c.p c.q
 | .outside c=>fiveChildrenMeter S a b c.p c.q
 | .remaining=>⟨[],1⟩

theorem local_children_value (S : Tree) (a b : Nat) (sel : LocalSelection) :
 (localChildrenMeter S a b sel).value=localChildren S a b sel := by
 cases sel <;> simp only [localChildrenMeter,localChildren,pendant_child_value,five_children_value]

theorem local_children_work (S : Tree) (a b : Nat) (sel : LocalSelection) :
 (localChildrenMeter S a b sel).work≤fiveChildrenBudget (leaves S).length+2 := by
 have p:=pendant_child_work S a b
 cases sel
 all_goals simp only [localChildrenMeter]
 all_goals first | exact Nat.le_trans (five_children_work S a b _ _) (by omega) | unfold fiveChildrenBudget;omega
end Universal233.Rule5SelectedLocalWork
