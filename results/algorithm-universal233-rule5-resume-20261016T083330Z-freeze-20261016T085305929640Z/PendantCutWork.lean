import PendantAddressScans
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork

def cutGuardMeter (S : Tree) (a b : Nat) (v : RMAF.Vertex) : Measured Bool :=
 if v.isEmpty then ⟨false,1⟩ else
 let p:=dropLastMeter v;let m:=minimalMeter [a,b] S
 let c:=containsAddressMeter p.value m.value
 if c.value then let m2:=minimalMeter [a,b] S;let d:=containsAddressMeter v m2.value
  ⟨!d.value,p.work+m.work+c.work+m2.work+d.work+3⟩
 else ⟨false,p.work+m.work+c.work+2⟩

theorem cut_guard_value (S : Tree) (a b : Nat) (v : RMAF.Vertex) :
 (cutGuardMeter S a b v).value=(!v.isEmpty && (minimalVertices [a,b] S).contains v.dropLast &&
   !(minimalVertices [a,b] S).contains v) := by
 simp only [cutGuardMeter,drop_last_value,minimal_value,contains_address_value]
 split <;> simp_all
 split <;> simp_all

def cutGuardBudget (n : Nat) : Nat :=2*minimalBudget 2 n+2*(2*n+2)*(2*n)+2*n+8

theorem cut_guard_work (S : Tree) (a b : Nat) (v : RMAF.Vertex)
 (hv : v.length≤(leaves S).length) : (cutGuardMeter S a b v).work≤cutGuardBudget (leaves S).length := by
 have m:=minimal_work [a,b] S
 have n:=vertices_count S
 have mc:=minimal_count [a,b] S
 have vc : ∀p,p∈(minimalMeter [a,b] S).value →p.length≤(leaves S).length := by
   intro p hp;have:=minimal_address [a,b] S hp;omega
 have dl:=drop_last_work v
 have dlen : (dropLastMeter v).value.length≤(leaves S).length := by
   rw [drop_last_value,List.length_dropLast];omega
 have c:=contains_address_work (dropLastMeter v).value (minimalMeter [a,b] S).value (leaves S).length dlen vc
 have d:=contains_address_work v (minimalMeter [a,b] S).value (leaves S).length hv vc
 have count : (minimalMeter [a,b] S).value.length≤2*(leaves S).length := by rw [minimal_value];omega
 have cc:=Nat.mul_le_mul_left (2*(leaves S).length+2) count
 change (minimalMeter [a,b] S).work≤minimalBudget 2 (leaves S).length at m
 simp only [cutGuardMeter,cutGuardBudget]
 split <;> (try dsimp only) <;> try omega
 split <;> (try dsimp only) <;> simp only [Nat.mul_assoc] at * <;> omega

def cutFilterMeter (S : Tree) (a b : Nat) : List RMAF.Vertex→Measured (List RMAF.Vertex)
 | []=>⟨[],1⟩
 | v::vs=>let c:=cutGuardMeter S a b v;let r:=cutFilterMeter S a b vs
           ⟨if c.value then v::r.value else r.value,c.work+r.work+2⟩

theorem cut_filter_value (S : Tree) (a b : Nat) (vs : List RMAF.Vertex) :
 (cutFilterMeter S a b vs).value=vs.filter fun v=>!v.isEmpty &&
   (minimalVertices [a,b] S).contains v.dropLast && !(minimalVertices [a,b] S).contains v := by
 induction vs with
 | nil=>rfl
 | cons v vs ih=>simp only [cutFilterMeter,List.filter_cons,cut_guard_value,ih]

theorem cut_filter_work (S : Tree) (a b : Nat) (vs : List RMAF.Vertex)
 (cap : ∀v,v∈vs →v.length≤(leaves S).length) :
 (cutFilterMeter S a b vs).work≤(cutGuardBudget (leaves S).length+2)*vs.length+1 := by
 induction vs with
 | nil=>simp [cutFilterMeter]
 | cons v vs ih=>
   have c:=cut_guard_work S a b v (cap v (by simp))
   have tail:=ih (fun p hp=>cap p (by simp [hp]))
   simp only [cutFilterMeter,List.length_cons,Nat.mul_succ]
   omega

def cutsMeter (S : Tree) (a b : Nat) : Measured (List RMAF.Vertex) :=
 let v:=verticesMeter S;let f:=cutFilterMeter S a b v.value
 ⟨f.value,v.work+f.work+1⟩

theorem cuts_value (S : Tree) (a b : Nat) : (cutsMeter S a b).value=CherryBranching.cuts S a b := by
 simp only [cutsMeter,cut_filter_value,vertices_value,CherryBranching.cuts,pendantOriginal]

def cutsBudget (n : Nat) : Nat :=64*n*n+(cutGuardBudget n+2)*(2*n)+2

theorem cuts_work (S : Tree) (a b : Nat) : (cutsMeter S a b).work≤cutsBudget (leaves S).length := by
 have v:=vertices_work S
 have len:=vertices_count S
 have c:=cut_filter_work S a b (verticesMeter S).value (fun p hp=>by have:=vertices_address S hp;omega)
 have count : (verticesMeter S).value.length≤2*(leaves S).length := by rw [vertices_value];omega
 have slots:=Nat.mul_le_mul_left (cutGuardBudget (leaves S).length+2) count
 simp only [cutsMeter,cutsBudget]
 omega

theorem cuts_count (S : Tree) (a b : Nat) : (cutsMeter S a b).value.length≤2*(leaves S).length := by
 rw [cuts_value]
 have h:=List.length_filter_le (fun v=>!v.isEmpty && (minimalVertices [a,b] S).contains v.dropLast && !(minimalVertices [a,b] S).contains v) (vertices S)
 have c:=vertices_count S
 change (pendantOriginal S a b).length≤_
 unfold pendantOriginal
 omega

theorem cuts_address (S : Tree) (a b : Nat) {p : RMAF.Vertex} (hp : p∈(cutsMeter S a b).value) :
 p.length+1≤(leaves S).length := by
 rw [cuts_value] at hp
 have val:=((CherryBranching.cuts_spec S a b p).1 hp).1
 obtain ⟨U,sub⟩:=val
 exact subtree_depth sub
end Universal233.Rule5PendantLocalWork
