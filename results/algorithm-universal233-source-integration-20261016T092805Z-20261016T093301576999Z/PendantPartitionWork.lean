import PendantSubtrees
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching

def payloadCap (n : Nat) := n*(2*n)
def blocksBudget (n : Nat) := (4*n*n+2*n+3)*(2*n)+1

def pendantPayloadMeter (S : Tree) (a b : Nat) : Measured (List Nat) :=
 let e:=cutsMeter S a b;let bs:=blocksMeter S e.value;let f:=flattenMeter bs.value
 ⟨f.value,e.work+bs.work+f.work+2⟩

theorem pendant_payload_value (S : Tree) (a b : Nat) :
 (pendantPayloadMeter S a b).value=((cuts S a b).map (subtreeLabels S)).flatten := by
 simp only [pendantPayloadMeter,flatten_value,blocks_value,cuts_value]

theorem actual_blocks_work (S : Tree) (a b : Nat) :
 (blocksMeter S (cutsMeter S a b).value).work≤blocksBudget (leaves S).length := by
 have blk:=blocks_work S (cutsMeter S a b).value (leaves S).length
   (fun p hp=>by have:=cuts_address S a b hp;omega)
 have len:=cuts_count S a b
 have m:=Nat.mul_le_mul_left (4*(leaves S).length*(leaves S).length+2*(leaves S).length+3) len
 unfold blocksBudget
 omega

theorem actual_blocks_payload (S : Tree) (a b : Nat) :
 (blocksMeter S (cutsMeter S a b).value).value.length≤2*(leaves S).length ∧
 (blocksMeter S (cutsMeter S a b).value).value.flatten.length≤payloadCap (leaves S).length ∧
 (blocksMeter S (cutsMeter S a b).value).value.flatten⊆leaves S := by
 have blk:=blocks_payload S (cutsMeter S a b).value
 have len:=cuts_count S a b
 have mul:=Nat.mul_le_mul_left (leaves S).length len
 unfold payloadCap
 exact ⟨by omega,by omega,blk.2.2⟩

def pendantPayloadBudget (n : Nat) :=cutsBudget n+blocksBudget n+payloadCap n+2*n+3

theorem pendant_payload_work (S : Tree) (a b : Nat) :
 (pendantPayloadMeter S a b).work≤pendantPayloadBudget (leaves S).length := by
 have e:=cuts_work S a b
 have blk:=actual_blocks_work S a b
 have p:=actual_blocks_payload S a b
 have f:=flatten_work (blocksMeter S (cutsMeter S a b).value).value
 simp only [pendantPayloadMeter,pendantPayloadBudget]
 omega

theorem pendant_payload_domain (S : Tree) (a b : Nat) :
 (pendantPayloadMeter S a b).value.length≤payloadCap (leaves S).length ∧
 (pendantPayloadMeter S a b).value⊆leaves S := by
 have blk:=actual_blocks_payload S a b
 simp only [pendantPayloadMeter,flatten_value]
 exact ⟨blk.2.1,blk.2.2⟩

/-- Actual core predicate materializes the literal cut/subtree-label/flatten
payload at each visited input leaf; no hidden free precomputed color or set. -/
def coreFilterMeter (S : Tree) (a b : Nat) : List Nat→Measured (List Nat)
 | []=>⟨[],1⟩
 | x::xs=>let p:=pendantPayloadMeter S a b;let c:=containsMeter x p.value
           let r:=coreFilterMeter S a b xs
           ⟨if !c.value then x::r.value else r.value,p.work+c.work+r.work+2⟩

theorem core_filter_value (S : Tree) (a b : Nat) (xs : List Nat) :
 (coreFilterMeter S a b xs).value=xs.filter fun x=>!((cuts S a b).map (subtreeLabels S)).flatten.contains x := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>simp only [coreFilterMeter,List.filter_cons,contains_value,pendant_payload_value,ih]

theorem core_filter_work (S : Tree) (a b : Nat) (xs : List Nat) :
 (coreFilterMeter S a b xs).work≤(pendantPayloadBudget (leaves S).length+2*payloadCap (leaves S).length+3)*xs.length+1 := by
 induction xs with
 | nil=>simp [coreFilterMeter]
 | cons x xs ih=>
   have p:=pendant_payload_work S a b
   have dom:=pendant_payload_domain S a b
   have c:=contains_work x (pendantPayloadMeter S a b).value
   simp only [coreFilterMeter,List.length_cons,Nat.mul_succ]
   omega

def coreMeter (S : Tree) (a b : Nat) : Measured (List Nat) :=
 let l:=leavesMeter S;let f:=coreFilterMeter S a b l.value
 ⟨f.value,l.work+f.work+1⟩

theorem core_value (S : Tree) (a b : Nat) : (coreMeter S a b).value=coreLabels S a b := by
 simp only [coreMeter,core_filter_value,leaves_value,coreLabels]

def coreBudget (n : Nat) :=4*n*n+(pendantPayloadBudget n+2*payloadCap n+3)*n+2

theorem core_work (S : Tree) (a b : Nat) : (coreMeter S a b).work≤coreBudget (leaves S).length := by
 have l:=leaves_work S
 have f:=core_filter_work S a b (leaves S)
 simp only [coreMeter,leaves_value,coreBudget]
 omega

theorem core_domain (S : Tree) (a b : Nat) :
 (coreMeter S a b).value.length≤(leaves S).length ∧ (coreMeter S a b).value⊆leaves S := by
 rw [core_value]
 exact ⟨List.length_filter_le _ _,fun x hx=>(List.mem_filter.1 hx).1⟩

def partitionMeter (S : Tree) (a b : Nat) : Measured (List (List Nat)) :=
 let e:=cutsMeter S a b;let bs:=blocksMeter S e.value;let c:=coreMeter S a b
 ⟨bs.value++[c.value],e.work+bs.work+c.work+bs.value.length+3⟩

theorem partition_value (S : Tree) (a b : Nat) : (partitionMeter S a b).value=pendantPartition S a b := by
 simp only [partitionMeter,cuts_value,blocks_value,core_value,pendantPartition]

def partitionBudget (n : Nat) :=cutsBudget n+blocksBudget n+coreBudget n+2*n+3

theorem partition_work (S : Tree) (a b : Nat) :
 (partitionMeter S a b).work≤partitionBudget (leaves S).length := by
 have e:=cuts_work S a b
 have blk:=actual_blocks_work S a b
 have p:=actual_blocks_payload S a b
 have c:=core_work S a b
 simp only [partitionMeter,partitionBudget]
 omega

theorem partition_domain (S : Tree) (a b : Nat) :
 (partitionMeter S a b).value.length≤2*(leaves S).length+1 ∧
 (partitionMeter S a b).value.flatten.length≤payloadCap (leaves S).length+(leaves S).length ∧
 (partitionMeter S a b).value.flatten⊆leaves S := by
 have bs:=actual_blocks_payload S a b
 have core:=core_domain S a b
 simp only [partitionMeter,List.length_append,List.length_cons,List.length_nil,
   List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append]
 refine ⟨by omega,by omega,?_⟩
 intro x hx
 rcases List.mem_append.1 hx with hx|hx
 · exact bs.2.2 hx
 · exact core.2 hx
end Universal233.Rule5PendantLocalWork
